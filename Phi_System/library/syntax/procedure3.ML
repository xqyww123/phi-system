signature PROCEDURE_SYNTAX = sig
include PROCEDURE_SYNTAX

(*Given a procedure spec (a triple), proc f arg \<lbrace> X arg \<longmapsto> Y \<rbrace>
  it universally quantifies the term, returning \<open>\<forall>arg. proc f arg \<lbrace> X arg \<longmapsto> Y \<rbrace>\<close>
  using the argument encoding*)
val quantify_args_of_proc_term : bool (*whether to record the names in the quantification*)
                         -> term -> term
val quantify_args_of_proc_term_meta : bool (*whether to record the names in the quantification*)
                         -> term -> term

val rule_of_package_arguement : Proof.context -> term -> thm

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
      val Vs = if is_var f then NONE
               else case f of _ $ Vs => if is_argT' (fastype_of Vs)
                                        then SOME (dest_arg_tuple Vs)
                                        else SOME []
                            | _      => SOME []
      val (pack, X') = package_values "" \<^typ>\<open>unit\<close> true Vs X
      fun parameterize_var (Var (v,T)) = Var (v, fastype_of pack --> T) $ Bound 0
        | parameterize_var (X $ Bound i) = parameterize_var X $ Bound 0
      val f' = if is_var f then parameterize_var f
               else case f of F $ Vs  => if is_argT' (fastype_of Vs)
                                         then F $ Bound 0
                                         else f
                            | _      => f
      val T = fastype_of pack
      val abs1 = Abs ("", T,
            (H $ f' $ (incr_boundvars 1 X' $ Bound 0) $ incr_boundvars 1 Y $ incr_boundvars 1 E))
      val (T2,abs2) =
            if record_name
            then let
             val names = dest_arg_tuple pack
                      |> map (fn Free (N,_) => N
                               | Var ((N,i),_) => if i = 0 then N else N ^ string_of_int i
                               | _ => "")
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
    (\<And>a. \<^bold>p\<^bold>r\<^bold>o\<^bold>c f a \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[\<phi>V_snd a] T\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[\<phi>V_fst a] U\<heavy_comma> BB \<longmapsto> YY \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s EE ) \<equiv>
    (\<And>a b. \<^bold>p\<^bold>r\<^bold>o\<^bold>c f (\<phi>V_pair a b) \<lbrace> x \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[b] T\<heavy_comma> y \<Ztypecolon> \<^bold>v\<^bold>a\<^bold>l[a] U\<heavy_comma> BB \<longmapsto> YY \<rbrace> \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s EE )
*)
fun rule_of_package_arguement ctxt proc =
  let val packed = quantify_args_of_proc_term_meta false proc
                |> Thm.cterm_of ctxt
      val ctxt' = Simplifier.init_simpset @{thms split_paired_all_\<phi>arg[folded atomize_eq]
                                                 \<phi>V_simps[folded atomize_eq]} ctxt
   in Raw_Simplifier.rewrite_cterm (false,false,false) (K (K NONE)) ctxt' packed end

end
