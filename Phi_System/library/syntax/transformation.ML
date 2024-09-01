signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val dest_BI_ty : typ -> typ (*typ of concrete algebra*)

  val is_intro_transformation : term -> bool
  val is_elim_transformation : term -> bool
  val pass_ensures_intro_transformation : Phi_Reasoner.rule_pass
  val pass_ensures_elim_transformation : Phi_Reasoner.rule_pass

  val dest_transformation_typ : term -> typ
  val dest_transformation   : term  -> term * term * term
  val dest_transformation_c : cterm -> cterm * cterm * cterm
  val transformation_conv : conv -> conv -> conv -> conv

  val conv_ToR_add_tag : conv


  val enable_auto_chk_and_conv : bool Config.T

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

fun dest_BI_ty (\<^Type>\<open>BI ty\<close>) = ty
  | dest_BI_ty ty = raise TYPE ("Not of a type of BI assertion", [ty], [])

val dest_transformation   =
         PLPR_Syntax.dest_tags
      #> Phi_Help.dest_triop @{const_name "Transformation"}
val dest_transformation_c =
         PLPR_Syntax.dest_tags_c
      #> Phi_Help.dest_triop_c @{const_name "Transformation"}


fun dest_transformation_typ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = dest_transformation_typ X
  | dest_transformation_typ (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = dest_transformation_typ X
  | dest_transformation_typ (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ X) = dest_transformation_typ X
  | dest_transformation_typ (Const(\<^const_name>\<open>Transformation\<close>, \<^Type>\<open>fun \<^Type>\<open>BI a\<close> _\<close>) $ _ $ _ $ _) = a
  | dest_transformation_typ X = raise TERM ("dest_transformation_typ", [X])

fun is_intro_transformation rule =
  let val (prems, concl) = Logic.strip_horn rule
   in case dest_transformation concl
   of (Var v, _, _) =>
        exists (PLPR_Syntax.eixsts_antecedent (
            fn prem => case try dest_transformation (Logic.strip_assums_concl prem)
                             of SOME (Var v', _, _) => v' = v
                              | _ => false)) prems
    | _ => false
  end

fun is_elim_transformation rule =
  let val (prems, concl) = Logic.strip_horn rule
   in case dest_transformation concl
   of (_, Var v, _) =>
        exists (PLPR_Syntax.eixsts_antecedent (
            fn prem => case try dest_transformation (Logic.strip_assums_concl prem)
                             of SOME (_, Var v', _) => v' = v
                              | _ => false)) prems
    | _ => false
  end

fun pass_ensures_intro_transformation _ (rules, (mode, priority), (pattern, except), guard, ctxt) =
  let fun chk rule = if is_intro_transformation (Thm.prop_of rule) then rule
                     else rule RS' (Context.proof_of ctxt, @{thm' mk_intro_transformation})
   in (map chk rules, (mode, priority), (pattern, except), guard, ctxt)
  end

fun pass_ensures_elim_transformation _ (rules, (mode, priority), (pattern, except), guard, ctxt) =
  let fun chk rule = if is_elim_transformation (Thm.prop_of rule) then rule
                     else rule RS' (Context.proof_of ctxt, @{thm' mk_elim_transformation})
   in (map chk rules, (mode, priority), (pattern, except), guard, ctxt)
  end

fun pass_pattern_of_intro_ToR _ (data as (rules, (mode, priority), (pattern, except), guard, ctxt)) =
  case (rules, pattern)
    of ([rule], []) =>
        if is_intro_transformation (Thm.prop_of rule)
        then let val i = Thm.maxidx_of rule + 1
                 fun var N = Var((N,i),TVar((N,i),[]))
                 val pattern = case Thm.concl_of rule
                                 of Trueprop $ (Tag $ (Trans $ X $ Y $ P) $ A) =>
                                    [(Trueprop $ (Tag $ (Trans $ var "X" $ Y $ var "P") $ A), NONE)]
                                  | _ => []
              in (rules, (mode, priority), (pattern, except), guard, ctxt)
             end
        else data
     | _ => data

fun pass_pattern_of_elim_ToR _ (data as (rules, (mode, priority), (pattern, except), guard, ctxt)) =
  case (rules, pattern)
    of ([rule], []) =>
        if is_elim_transformation (Thm.prop_of rule)
        then let val i = Thm.maxidx_of rule + 1
                 fun var N = Var((N,i),TVar((N,i),[]))
                 val pattern = case Thm.concl_of rule
                                 of Trueprop $ (Tag $ (Trans $ X $ Y $ P) $ A) =>
                                    [(Trueprop $ (Tag $ (Trans $ X $ var "Y" $ var "P") $ A), NONE)]
                                  | _ => []
              in (rules, (mode, priority), (pattern, except), guard, ctxt)
             end
        else data
     | _ => data

fun transformation_conv C_s C_t C_p ctm = (
  dest_transformation_c ctm;
  Phi_Conv.tag_conv (
    Conv.combination_conv (Conv.combination_conv (Conv.combination_conv Conv.all_conv C_s) C_t) C_p) ctm
)


(** Auto Classify Transformation Rules **)

val enable_auto_chk_and_conv = Config.declare_bool ("enable_auto_chk_and_conv_\<phi>ToR", \<^here>) (K true)

fun err ctm = raise CTERM("Fail to classify the Transformation rule automatically into \<T>\<P>, \<T>\<P>'", [ctm])
fun err' tm = raise TERM("Fail to classify the Transformation rule automatically into \<T>\<P>, \<T>\<P>'", [tm])

fun is_Var X =
  case Term.strip_comb X
    of (Var _, args) => forall (fn Bound _ => true | _ => false) args
     | _ => false

fun conv_ToR_add_tag ctm =
  let datatype kind = ProdTy | Ty | Var | Oth
      fun cond_Ty (Const(\<^const_name>\<open>\<phi>Prod'\<close>, _) $ _ $ _) = ProdTy
        | cond_Ty _ = Ty
      fun dest_ty (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ U) = cond_Ty U
        | dest_ty X = if is_Var X then Var else Oth
      val (X,Y,_) = dest_transformation (Thm.term_of ctm)
   in case (dest_ty X, dest_ty Y)
   of (ProdTy, ProdTy) => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>'\<close>, symmetric]} ctm
    | (Var, ProdTy) => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>'\<close>, symmetric]} ctm
    | (ProdTy, Var) => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>'\<close>, symmetric]} ctm
    | (Oth, _) => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>\<close>, symmetric]} ctm
    | (_, Oth) => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>\<close>, symmetric]} ctm
    | (Ty, Ty)  => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>\<close>, symmetric]} ctm
    | (Ty, Var)  => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>\<close>, symmetric]} ctm
    | (Var, Ty)  => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>\<close>, symmetric]} ctm
    | (Var, Var)  => Conv.rewr_conv @{thm' Action_Tag_def[where A=\<open>\<T>\<P>\<close>, symmetric]} ctm
    | _ => err ctm
  end

fun conv_ToR_add_tag' ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ _ $ _ =>
        conv_ToR_add_tag ctm
     | _ => let
        fun chk_all_transformation_is_tagged (Const (\<^const_name>\<open>Action_Tag\<close>, _) $ (Const (\<^const_name>\<open>Transformation\<close>, _) $ _ $ _ $ _) $ _) = true
          | chk_all_transformation_is_tagged (Const (\<^const_name>\<open>Transformation\<close>, _) $ _ $ _ $ _) = false
          | chk_all_transformation_is_tagged (X $ Y) = chk_all_transformation_is_tagged X andalso chk_all_transformation_is_tagged Y
          | chk_all_transformation_is_tagged (Abs (_, _, X)) = chk_all_transformation_is_tagged X
          | chk_all_transformation_is_tagged _ = true
     in if chk_all_transformation_is_tagged (Thm.term_of ctm)
        then Conv.all_conv ctm
        else err ctm
    end

fun chk_ToR_prop term = let
        datatype TP_mode = TP | TP' | CLEAN

        fun source_val (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = source_val X
          | source_val (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = source_val X
          | source_val (Abs (_,_,X)) = source_val X
          | source_val (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = source_val X
          | source_val (Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ _ $ _) =
              (case X of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ _ => SOME x
                       | Free _ => SOME X
                       | Var _  => SOME X
                       | _ => NONE)
          | source_val (A $ B) = (case source_val A of NONE => source_val B
                                                     | some => some)
          | source_val _ = NONE
        val source_val = source_val term

        fun set (concl,NONE) X = (concl,SOME X)
          | set (_,SOME _) _ = err' term
        fun chk_TP'_src (Const(\<^const_name>\<open>\<phi>Type\<close>, _)
                $ X
                $ (Const(\<^const_name>\<open>\<phi>Prod'\<close>, _) $ _ $ _)) =
            (case X of Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _ => ()
                     | tm as Free _ => if SOME tm = source_val then ()
                                       else raise TERM ("Bad \<T>\<P>' request", [X])
                     | tm as Var _ => if SOME tm = source_val then ()
                                       else raise TERM ("Bad \<T>\<P>' request", [X])
                     | _ => raise TERM ("Bad \<T>\<P>' request", [X, term]))
          | chk_TP'_src X =
                if SOME X = source_val then ()
                                       else raise TERM ("Bad \<T>\<P>' request", [X])
        fun scan C (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ Const(\<^const_name>\<open>\<T>\<P>\<close>, _)) = scan (set C TP) X
          | scan C (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ Const(\<^const_name>\<open>\<T>\<P>'\<close>, _)) = scan (set C TP') X
          | scan C (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ Const(\<^const_name>\<open>\<A>clean\<close>, _)) = scan (set C CLEAN) X
          | scan _ (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = ()
          | scan C (Const(\<^const_name>\<open>Transformation\<close>, _) $ X $ _ $ _) = (
              case C
                of (concl,SOME TP') => (if concl then () else chk_TP'_src X)
                 | (_,SOME TP) => ()
                 | (_,SOME CLEAN) => ()
                 | (_,NONE) =>
              error "The use of transformation must be tagged in a transformation rule.\n\
                    \You can disable this check by \
                    \\<open>setup \<open>Config.put_global (Phi_Syntax.enable_auto_chk_and_conv) false\<close>\<close>.\n\
                    \if you are sure about what you are doing." )
          | scan (concl,C) (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ A $ B) = (scan (false,C) A; scan (concl,C) B)
          | scan C (X $ Y) = (scan C X ; scan C Y)
          | scan C (Abs (_, _, X)) = scan C X
          | scan _ _ = ()
   in scan (true,NONE) term
  end

fun ToR_rule_add_tag ctxt th =
  Conv.fconv_rule (Phi_Conv.hhf_conv (Phi_Conv.hhf_concl_conv (K (HOLogic.Trueprop_conv conv_ToR_add_tag')))
                                     (K (HOLogic.Trueprop_conv conv_ToR_add_tag')) ctxt) th
  |> (fn th => (chk_ToR_prop (Thm.prop_of th) ; th))

val _ = Theory.setup (Context.theory_map (
  Phi_Reasoner.add_pass (Free("Add ToR tag auto", dummyT), \<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>,
    fn _ => fn (rules, prio, pats, guard, ctxt) =>
        if Config.get_generic ctxt enable_auto_chk_and_conv
        then let val _ = List.app (chk_ToR_prop o fst) (fst pats)
                 val _ = List.app chk_ToR_prop (snd pats)
                 val rules' = map (fn rule =>
                        if Thm.is_dummy rule
                        then rule
                        else ToR_rule_add_tag (Context.proof_of ctxt) rule) rules
                 val _ = List.app (chk_ToR_prop o Thm.prop_of) rules'
           in (rules', prio, pats, guard, ctxt)
          end
        else (rules, prio, pats, guard, ctxt) )

#> Phi_Reasoner.add_pass (Free("Add ToR tag auto", dummyT), \<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>\<close>,
    fn _ => fn data as (rules, _, _, _, _) => (
        List.app (chk_ToR_prop o Thm.prop_of) rules ;
        data ))

#> Phi_Reasoner.add_pass (Free("Add ToR tag auto", dummyT), \<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>'\<close>,
    fn _ => fn data as (rules, _, _, _, _) => (
        List.app (chk_ToR_prop o Thm.prop_of) rules ;
        data ))

 (*
#>Phi_Reasoner.add_pass (Free("Pattern of intro-ToR", dummyT),
          \<^pattern_prop>\<open>?var_X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>\<close>, pass_pattern_of_intro_ToR)
#>Phi_Reasoner.add_pass (Free("Pattern of elim-ToR", dummyT),
          \<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _ @tag \<T>\<P>\<close>, pass_pattern_of_elim_ToR)
#>Phi_Reasoner.add_pass (Free("Pattern of intro-ToR", dummyT),
          \<^pattern_prop>\<open>?var_X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @tag \<T>\<P>'\<close>, pass_pattern_of_intro_ToR)
#>Phi_Reasoner.add_pass (Free("Pattern of elim-ToR", dummyT),
          \<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _ @tag \<T>\<P>'\<close>, pass_pattern_of_elim_ToR)
#>Phi_Reasoner.add_pass (Free("Pattern of intro-ToR", dummyT),
          \<^pattern_prop>\<open>?var_X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ \<close>, pass_pattern_of_intro_ToR)
#>Phi_Reasoner.add_pass (Free("Pattern of elim-ToR", dummyT),
          \<^pattern_prop>\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _ \<close>, pass_pattern_of_elim_ToR) *)
))

(* pass_pattern_of_intro_ToR *)

end