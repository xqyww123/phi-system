signature PROCEDURE_SYNTAX = sig
include PROCEDURE_SYNTAX

(*Given a procedure spec (a triple), proc f arg \<lbrace> X arg \<longmapsto> Y \<rbrace>
  it universally quantifies the term, returning \<open>\<forall>arg. proc f arg \<lbrace> X arg \<longmapsto> Y \<rbrace>\<close>
  using the argument encoding*)
val quantify_args_of_proc_term : bool (*whether to record the names in the quantification*)
                         -> term -> term
val quantify_args_of_proc_term_meta : bool (*whether to record the names in the quantification*)
                         -> term -> term

(* \<p>\<r>\<o>\<c> f ?a ?b \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[?b] T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[?a] U\<heavy_comma> BB \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE
--------------------------------------------------------------------------------------
   \<forall>pack. \<p>\<r>\<o>\<c> f pack \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[\<phi>V_snd pack] T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[\<phi>V_fst pack] U\<heavy_comma> BB \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE
*)
val package_argument : Proof.context -> thm -> thm

end

structure Procedure_Syntax : PROCEDURE_SYNTAX = struct
open Procedure_Syntax

fun quantify_args_of_proc_term' record_name proc =
  let val (H as Const (\<^const_name>\<open>\<phi>Procedure\<close>, _)) $ f $ X $ Y $ E = proc
      fun is_var (X $ Bound _) = is_var X
        | is_var (Var _) = true
        | is_var _ = false
      fun is_argT' (Type ("dummy", _)) = true
        | is_argT' T = is_argT T
      fun is_args Vs =
          is_argT' (fastype_of Vs) andalso
          (case try dest_arg_tuple Vs of SOME vs =>
                  forall (fn Free _ => true | Var _ => true | _ => false) vs
              | _ => false)
      fun is_Free_or_Const (Const _) = true
        | is_Free_or_Const (Free _) = true
        | is_Free_or_Const _ = false
      val Vs = if is_var f then NONE
               else case f of F $ Vs => if is_Free_or_Const (head_of F)
                                        then if is_args Vs
                                        then SOME (dest_arg_tuple Vs)
                                        else SOME []
                                        else NONE
                            | _      => NONE
      val (pack, X') = package_values "" true Vs X
      fun parameterize_var (Var (v,T))   = Var (v, fastype_of pack --> T) $ Bound 0
        | parameterize_var (X $ Bound i) = parameterize_var X $ Bound (i + 1)
      val f' = if is_var f then parameterize_var f
               else case f of F $ Vs =>
                              if is_Free_or_Const (head_of F)
                              then if is_args Vs
                              then incr_boundvars 1 F $ Bound 0
                              else incr_boundvars 1 f
                              else incr_boundvars 1 (
                                      snd (package_values "" true (SOME (dest_arg_tuple pack)) f))
                                   $ Bound 0
                            | _      =>
                              incr_boundvars 1 (
                                snd (package_values "" true (SOME (dest_arg_tuple pack)) f))
                              $ Bound 0
      val T = fastype_of pack
      val abs1 = Abs ("", T,
            (H $ f' $ (incr_boundvars 1 X' $ Bound 0) $ incr_boundvars 1 Y $ incr_boundvars 1 E))
      val (T2,abs2) =
            if record_name
            then let
             val names = dest_arg_tuple pack
                      |> map (fn Free (N,_) => N
                               | Var ((N,i),_) => if i = 0 then N else N ^ string_of_int i
                               | _ => error "Internal error #2dc7cd58-8e36-4124-b760-a49e5f2abe1c")
             val T2 = Phi_Syntax.mk_namedT T names
              in (T2, Const (\<^const_name>\<open>case_named\<close>, (T --> HOLogic.boolT) --> T2 --> HOLogic.boolT)
                        $ abs1)
             end
            else (T,abs1)
   in (abs2, T2)
  end

fun quantify_args_of_proc_meta'1 record_name (Const (\<^const_name>\<open>Trueprop\<close>, _) $ X) =
      quantify_args_of_proc_meta'1 record_name X
  | quantify_args_of_proc_meta'1 record_name ((tag as Const (\<^const_name>\<open>Action_Tag\<close>, _)) $ A $ B) =
      quantify_args_of_proc_meta'1 record_name A |> apfst (fn Y => tag $ Y $ B)
  | quantify_args_of_proc_meta'1 record_name proc =
      let val (abs2, T2) = quantify_args_of_proc_term' record_name proc
       in (HOLogic.Trueprop $ (abs2 $ Bound 0), T2)
      end

fun quantify_args_of_proc_term_meta record_name X =
  let val (Y, T2) = quantify_args_of_proc_meta'1 record_name X
   in Const (\<^const_name>\<open>Pure.all\<close>, (T2 --> propT) --> propT) $ (Abs ("", T2, Y))
  end

fun quantify_args_of_proc_term record_name (Const (\<^const_name>\<open>Trueprop\<close>, _) $ X) =
      HOLogic.Trueprop $ quantify_args_of_proc_term record_name X
  | quantify_args_of_proc_term record_name ((tag as Const (\<^const_name>\<open>Action_Tag\<close>, _)) $ A $ B) =
      tag $ quantify_args_of_proc_term record_name A $ B
  | quantify_args_of_proc_term record_name proc =
      let val (abs2, T2) = quantify_args_of_proc_term' record_name proc
       in Const (\<^const_name>\<open>HOL.All\<close>, (T2 --> HOLogic.boolT) --> HOLogic.boolT) $ abs2
      end


(*
    (\<And>a b. \<p>\<r>\<o>\<c> f a b \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[b] T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[a] U\<heavy_comma> BB \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE ) \<Longrightarrow>
    (\<forall>a. \<p>\<r>\<o>\<c> f a \<lbrace> x \<Ztypecolon> \<v>\<a>\<l>[\<phi>V_snd a] T\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[\<phi>V_fst a] U\<heavy_comma> BB \<longmapsto> YY \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> EE )
*)
fun rule_of_package_arguement ctxt proc =
  let val packed = quantify_args_of_proc_term false proc
                |> Thm.cterm_of ctxt
      fun expand_quant ctxt c = let open Conv Phi_Helper_Conv in
            try_conv (rewr_conv @{thm split_paired_all_\<phi>arg[folded atomize_eq]}
                      then_conv forall_conv (expand_quant o snd) ctxt)
          end c
      val ctxt' = Simplifier.init_simpset @{thms \<phi>V_simps[folded atomize_eq]} ctxt
   in packed
   |>(Conv.rewr_conv @{thm atomize_all[symmetric]}
      then_conv expand_quant ctxt'
      then_conv Raw_Simplifier.rewrite_cterm (false,false,false) (K (K NONE)) ctxt')
   |>(fn th => th RS @{thm equal_elim_rule2})
  end

fun package_argument ctxt proc_thm =
  let val proc = Thm.concl_of proc_thm
      val rule = rule_of_package_arguement ctxt proc
   in (proc_thm RS rule)
   |> Raw_Simplifier.rewrite_rule ctxt @{thms triv_forall_equality}
  end

end
