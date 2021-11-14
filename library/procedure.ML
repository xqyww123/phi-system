signature NU_PROCEDURE = sig
  val procedure_kind : string
  val cast_kind : string
  val proc_suffix : string
  val cast_suffix : string
  val compilation_suffix : string
  val parser : (string * Position.T) parser
  val declare_overloading : binding -> string (*comment*) -> local_theory -> string * local_theory
  val declare_overloading_cast : binding -> string (*comment*) -> local_theory -> string * local_theory
  val overload : thm -> (string * Position.T) -> Context.generic -> Context.generic
  val overload_cast : thm -> (string * Position.T) -> Context.generic -> Context.generic
  val procedure_thm : Proof.context -> (string * Position.T) -> thm list
  val cast_thm : Proof.context -> (string * Position.T) -> thm list
  val compilation_thm : Proof.context -> (string * Position.T) -> thm list
  val compilation_thm_of : Proof.context -> term -> thm list
  val define : Attrib.binding -> thm -> local_theory -> thm * local_theory
end

structure NuProcedure : NU_PROCEDURE = struct
open NuBasics

local open Parse in
val parser = position (short_ident || long_ident || sym_ident || keyword || string)
end

val proc_suffix = "_\<nu>proc"
val cast_suffix = "_\<nu>cast"
val compilation_suffix = "_\<nu>compilation"
val procedure_kind = "\<nu>procedure"
val cast_kind = "\<nu>cast"
val declare_overloading = Named_Theorems.declare o Binding.suffix_name proc_suffix
val declare_overloading_cast = Named_Theorems.declare o Binding.suffix_name cast_suffix
val suffix_namepos = apfst o suffix
fun gen_overload suf th name ctx =
  Named_Theorems.add_thm (Named_Theorems.check (Context.proof_of ctx)
    (suffix_namepos suf name)) th ctx
val overload = gen_overload proc_suffix
val overload_cast = gen_overload cast_suffix
fun namepos_to_fact_ref namepos = Facts.Named (namepos, NONE)
fun gen_get_thm suf ctx =
  Proof_Context.get_fact ctx o namepos_to_fact_ref o suffix_namepos suf
  handle e => raise (@{print} e)
val procedure_thm = gen_get_thm proc_suffix
val cast_thm = gen_get_thm cast_suffix
val compilation_thm = gen_get_thm compilation_suffix
fun compilation_thm_of ctx tm = compilation_thm ctx (term_name tm, Position.none)

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
    val (f,U,V) = Thm.concl_of proc_th |> Logic.unvarify_global |> dest_procedure 
    val arity = length (add_frees f [])
    val f' = fold lambda (map Free (add_frees f [])) f
    val def_binding = Binding.suffix_name compilation_suffix binding
    val proc_binding = Binding.suffix_name proc_suffix binding
    val (lthy, proc_th) =
      if Binding.is_empty binding then (lthy, proc_th)
      else lthy
            |> Local_Theory.define ((binding, NoSyn), ((def_binding,[]), f'))
            |-> (fn (tm,(_,def)) => fn lthy =>
                  (lthy, (proc_th RS (norm_def arity def RS @{thm rename_proc}))))
    val proc_th = proc_th
          (* |> Raw_Simplifier.rewrite_rule lthy @{thms Premise_Irew} *)
          |> Raw_Simplifier.rewrite_rule lthy
              (Proof_Context.get_thms lthy "NuSys.final_proc_rewrite")
          |> Raw_Simplifier.rewrite_rule lthy
              (Proof_Context.get_thms lthy "NuSys.final_proc_rewrite2")
  in lthy |> Local_Theory.notes_kind procedure_kind
                [((proc_binding,attrs), [([proc_th],[])])]
          |> apfst (fn [(_,[proc_th])] => proc_th)
  end
end
