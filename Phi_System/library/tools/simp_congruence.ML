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
  K (fn ctxt => Phi_SimpProc.cong @{thm \<phi>Val_simp_cong} ctxt)
\<close>

```
where \<phi>Val_simp_cong is a quasi-congruence rule of the above form.

*)

signature PHI_SIMP_PROC = sig
  val cong : thm -> Proof.context -> cterm -> thm option
  val cong_qualifier : thm -> Proof.context -> cterm -> thm option
  val preserving_lambda_name : thm -> conv
end

structure Phi_SimpProc : PHI_SIMP_PROC = struct
open Phi_Help

fun preserving_lambda_name rewrite_rule cterm =
  let fun get_lamb_names ret (Abs(N,_,X)) = N :: get_lamb_names ret X
        | get_lamb_names ret (X $ Y) =
            get_lamb_names (get_lamb_names ret Y) X
        | get_lamb_names ret _ = ret
      fun write_lamb (N::names) (Abs(N',T,X)) =
           (case write_lamb names X
              of (names', SOME ret) => (names', SOME (Abs (N,T,ret)))
               | (names', NONE) =>
                    (names', if N = N' then NONE else SOME (Abs(N,T,X))))
        | write_lamb names (X $ Y) =
            (case write_lamb names X
               of (names', SOME X') =>
                    (case write_lamb names' Y
                       of (names'', SOME Y') => (names'', SOME (X' $ Y'))
                        | (names'', NONE) => (names'', SOME (X' $ Y)))
                | (names', NONE) =>
                    (case write_lamb names' Y
                       of (names'', SOME Y') => (names'', SOME (X $ Y'))
                        | (names'', NONE) => (names'', NONE)))
        | write_lamb names _ = (names, NONE)

      val lamb = get_lamb_names [] (Thm.term_of cterm)
      val rewr = Conv.rewr_conv rewrite_rule cterm
   in case Thm.prop_of rewr
        of head $ RHS =>
            (case write_lamb lamb RHS
               of ([], SOME RHS') =>
                  Thm.renamed_prop (head $ RHS') rewr
                | ([], NONE) => rewr
                | _ => error "internal bug #796907e8-a2b9-43c9-b2a5-cb2902f5918e")
         | _ => error "internal bug #796907e8-a2b9-43c9-b2a5-cb2902f5918e"
  end


fun chk_simplified NONE = NONE
  | chk_simplified (SOME th) =
      case Thm.prop_of th of Const (@{const_name Pure.eq}, _) $ a $ b =>
        if Envir.aeconv (a,b) then NONE else SOME th

fun cong raw_cong ctx cterm =
  let
    val cong = Thm.incr_indexes (Thm.maxidx_of_cterm cterm + 1) raw_cong
    val (lhs,_) = Thm.cconcl_of cong |> dest_binop_c @{const_name "Pure.eq"}
    val cong = Thm.instantiate (Thm.first_order_match (lhs,cterm)) cong (*index is considered*)
  in
    SINGLE (ALLGOALS (SOLVED' (Simplifier.asm_simp_tac ctx))) cong |> chk_simplified
  end handle Pattern.MATCH => NONE

(* the version preserving name of the qualifier, useful for @{term ExSet}. *)
fun cong_qualifier cong_rule ctx cterm =
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
          => Option.map (norm_name name) (cong cong_rule ctx cterm) (* |> @{print} *)
      | _ => NONE
  end

val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>simp_cong\<close> (Scan.lift (Scan.succeed (
  Thm.declaration_attribute (fn rule => fn generic =>
    let val (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ LHS $ _) = Thm.concl_of rule
        fun install ctxt =
          ctxt addsimprocs [Simplifier.make_simproc ctxt "\<phi>simp_cong" {
              lhss = [LHS],
              proc = K (cong rule)
            }]
     in Context.mapping (Simplifier.map_theory_simpset install) install generic end)
)))
  ""
)

end
