(* FILE: library/tools/simp_congruence.ML
   Author: Qiyuan Xu

The module gives a generic simplification procedure for quasi-congruence rules
of container \<phi>-types in the following form,

    x\<^sub>1 : T\<^sub>1 \<equiv> y\<^sub>1 : U\<^sub>1
\<Longrightarrow> \<dots>
\<Longrightarrow> x\<^sub>n : T\<^sub>n \<equiv> y\<^sub>n : U\<^sub>n
\<Longrightarrow> f(x\<^sub>1,\<dots>,x\<^sub>n) : F(T\<^sub>1,\<dots>,T\<^sub>n) \<equiv> g(y\<^sub>1,\<dots>,y\<^sub>n) : G(T\<^sub>1,\<dots>,T\<^sub>n)

A typical usage is, for example,

```isabelle

simproc_setup Val_simp_cong ("x \<Ztypecolon> Val v T") = \<open>
  K (fn ctxt => Phi_SimpCong.simproc @{thm \<phi>Val_simp_cong} ctxt)
\<close>

```
where \<phi>Val_simp_cong is a quasi-congruence rule of the above form.

*)

signature PHI_SIMP_CONG = sig
  val simproc : thm -> Proof.context -> cterm -> thm option
  val simproc_qualifier : thm -> Proof.context -> cterm -> thm option
end

structure Phi_SimpCong : PHI_SIMP_CONG = struct
open Phi_Help

fun chk_simplified NONE = NONE
  | chk_simplified (SOME th) =
      case Thm.prop_of th of Const (@{const_name Pure.eq}, _) $ a $ b =>
        if Envir.aeconv (a,b) then NONE else SOME th

fun simproc raw_cong ctx cterm =
  let
    val cong = Thm.incr_indexes (Thm.maxidx_of_cterm cterm + 1) raw_cong
    val (lhs,_) = Thm.cconcl_of cong |> dest_binop_c @{const_name "Pure.eq"}
    val cong = Thm.instantiate (Thm.first_order_match (lhs,cterm)) cong (*index is considered*)
  in
    SINGLE (ALLGOALS (SOLVED' (Simplifier.asm_simp_tac ctx))) cong |> chk_simplified
  end handle Pattern.MATCH => NONE

(* the version preserving name of the qualifier, useful for @{term ExNu}. *)
fun simproc_qualifier cong ctx cterm =
  let
    fun norm_name name th =
      let
        val (Const (@{const_name Pure.eq}, x1) $ x2 $
              (Const (@{const_name \<phi>Type}, x4) $ image $ (Const qualifier $ nu)))
          = Thm.prop_of th
        val image = case image of Abs (_, ty, body) => Abs (name, ty, body) | tm => tm
        val nu = case nu of Abs (_, ty, body) => Abs (name, ty, body) | tm => tm
        val renamed = (Const (@{const_name Pure.eq}, x1) $ x2 $
                        (Const (@{const_name \<phi>Type}, x4) $ image $ (Const qualifier $ nu)))
      in
        Thm.renamed_prop renamed th
      end
  in
    case Thm.term_of cterm
      of (Const (@{const_name \<phi>Type}, _) $ _ $ (Const _ $ Abs (name, _, _)))
          => Option.map (norm_name name) (simproc cong ctx cterm) (* |> @{print} *)
      | _ => NONE
  end
  
end
