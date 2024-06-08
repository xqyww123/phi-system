signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val dest_param : term -> term
  val param_type : thm -> typ
  val param_type_c : thm -> ctyp

  val intro_param : cterm -> thm

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Phi_Syntax

local open Phi_Help in

val dest_param = perhaps (try HOLogic.dest_Trueprop)
              #> dest_monop @{const_name "ParamTag"}
val dest_param_c = dest_monop_c @{const_name "ParamTag"}
fun param_type_c th = Thm.cprem_of th 1 |> dest_param_c |> Thm.ctyp_of_cterm
fun param_type th = Thm.major_prem_of th |> dest_param |> type_of

fun intro_param tm =
  Thm.instantiate (TVars.make [((("'a",0), []), Thm.ctyp_of_cterm tm)],
                   Vars.make  [((("x",0), Thm.typ_of (Thm.ctyp_of_cterm tm)), tm)])
  @{thm ParamTag}

end

end