signature NU_PROCEDURE = sig
  val procedure_kind : string
  val proc_suffix : string
  val compilation_suffix : string
  val parser : (string * Position.T) parser
  val declare_overloading : binding -> string (*comment*) -> local_theory -> string * local_theory
  val overload : thm -> (string * Position.T) -> Context.generic -> Context.generic
  val procedure_thm : Proof.context -> (string * Position.T) -> thm list
  val compilation_thm : Proof.context -> (string * Position.T) -> thm list
  val compilation_thm_of : Proof.context -> term -> thm list
  val define : Attrib.binding -> thm -> local_theory -> thm * local_theory
end

structure NuProcedure : NU_PROCEDURE = struct
open NuBasics

local open Parse in
val parser = position (short_ident || long_ident || sym_ident || keyword)
end

val proc_suffix = "_\<nu>proc"
val compilation_suffix = "_\<nu>compilation"
val procedure_kind = "\<nu>procedure"
val declare_overloading = Named_Theorems.declare o Binding.suffix_name proc_suffix
val suffix_namepos = apfst o suffix
fun overload th name ctx =
  Named_Theorems.add_thm (Named_Theorems.check (Context.proof_of ctx)
    (suffix_namepos proc_suffix name)) th ctx
fun namepos_to_fact_ref namepos = Facts.Named (namepos, NONE)
fun procedure_thm ctx =
  Proof_Context.get_fact ctx o namepos_to_fact_ref o suffix_namepos proc_suffix
fun compilation_thm ctx =
  Proof_Context.get_fact ctx o namepos_to_fact_ref o suffix_namepos proc_suffix
fun compilation_thm_of ctx tm = compilation_thm ctx (term_name tm, Position.none)

fun define (binding,attrs) th lthy =
  let
    val (f,U,V) = Thm.concl_of th |> Logic.unvarify_global |> dest_procedure 
    val def_binding = Binding.suffix_name compilation_suffix binding
    val proc_binding = Binding.suffix_name proc_suffix binding
  in
    lthy
      |> Local_Theory.define ((binding, NoSyn), ((def_binding,[]), f))
      |-> (fn (tm,(_,def)) => 
            Local_Theory.notes_kind procedure_kind
              [((proc_binding,attrs), [([th RS (def RS @{thm NuPrim.rename_proc})],[])])]
            #> apfst (fn [(_,[th])] => th)
          )
  end
end
