signature NU_PROCEDURE = sig
  val procedure_kind : string
  val cast_kind : string
  val proc_suffix : string
  val cast_suffix : string
  val compilation_suffix : string
  val define : Attrib.binding -> thm -> local_theory -> thm * local_theory
end

structure NuProcedure : NU_PROCEDURE = struct
open NuBasics

val proc_suffix = "_\<nu>proc"
val cast_suffix = "_\<nu>cast"
val compilation_suffix = "_\<nu>compilation"
val procedure_kind = "\<nu>procedure"
val cast_kind = "\<nu>cast"
(* val compilation_thm = gen_get_thm compilation_suffix
fun compilation_thm_of ctx tm = compilation_thm ctx (term_name tm,
  Position.none) *)

fun strip_abs_var_n n tm = if n = 0 then [] else
  case Thm.dest_abs NONE tm of (v,body) =>
    v :: strip_abs_var_n (n-1) body
fun norm_def n def = let open Thm Drule Term
  val vars = strip_abs_var_n n (rhs_of def)
        |> map (fn tm =>
            Thm.var (term_of tm |> dest_Free |> #1 |> rpair 0,
              ctyp_of_cterm tm))
  in
    fold (fn a => fn b => Thm.combination b a) (map reflexive vars) def
  end

fun define (binding,attrs) proc_th lthy =
  let
    val (f,U,V) = Thm.concl_of (Drule.zero_var_indexes proc_th) |> dest_procedure 
    val vars = fold_aterms (fn Var v => insert (op =) (Var v)
                             | Free v => insert (op =) (Free v)
                             | _ => I) f  [];
    val arity = length vars
    fun lambda v body = Abs (term_name v, fastype_of v, abstract_over (v,body))
    val f' = fold lambda vars f |> Logic.unvarify_types_global
    val def_binding = Binding.suffix_name compilation_suffix binding
    val proc_binding = Binding.suffix_name proc_suffix binding
    fun rename def proc_th =
          (proc_th RS (def RS @{thm rename_func}))
      handle THM _ =>
          (proc_th RS (def RS @{thm rename_proc}))

    val (lthy, proc_th) =
      if Binding.is_empty binding then (lthy, proc_th)
      else lthy
            |> Local_Theory.define ((binding, NoSyn), ((def_binding,[]), f'))
            |-> (fn (tm,(_,def)) => fn lthy =>
                  (lthy, rename (norm_def arity def) proc_th))
    val proc_th = proc_th
          |> Raw_Simplifier.rewrite_rule lthy @{thms atomize_imp}
          (* |> Raw_Simplifier.rewrite_rule lthy
              (Proof_Context.get_thms lthy "NuSys.final_proc_rewrite")
          |> Raw_Simplifier.rewrite_rule lthy
              (Proof_Context.get_thms lthy "NuSys.final_proc_rewrite2") *)
  in lthy |> Local_Theory.notes_kind procedure_kind
                [((proc_binding,attrs), [([proc_th],[])])]
          |> apfst (fn [(_,[proc_th])] => proc_th)
  end
end
