signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val dest_nuTy : term -> term * term
  val dest_nuTy_c : cterm -> cterm * cterm
  val mk_nuTy : term * term -> term
  val mk_Nu_ty : typ * typ -> typ

  val is_construction_mode: term -> term -> bool
  val dest_CurrentConstruction   :  term -> term * term * term * term
  val dest_CurrentConstruction_c : cterm -> cterm * cterm * cterm * cterm
  val dest_PendingConstruction : term -> term * term * term * term * term
  val dest_PendingConstruction_c : cterm -> cterm * cterm * cterm * cterm * cterm
  val dest_set_member   :  term ->  term * term
  val dest_set_member_c : cterm -> cterm * cterm
  val dest_current_nu   : thm -> term (*depreciated, use #argument_spec in Working Mode instead.*)
  val dest_current_nu_c : thm -> cterm

  val block_var_of_Constuction : term  -> term
  val block_var_of_Constuction_c : cterm  -> cterm
  val current_block_var   : thm -> term
  val current_block_var_c : thm -> cterm

  val dest_procedure   : term -> term * term * term * term
  val dest_procedure_c : cterm -> cterm * cterm * cterm * cterm

  val dest_destined_phityp   : term -> term
  val dest_destined_phityp_c : cterm -> cterm

  val dest_view_shift   : term  -> term * term * term
  val dest_view_shift_c : cterm -> cterm * cterm * cterm

  val dest_implication   : term  -> term * term * term
  val dest_implication_c : cterm -> cterm * cterm * cterm
  val dest_Set_member    : term  -> term * term
  val dest_Set_member_c  : cterm -> cterm * cterm

  val strip_separations : term -> term list

  val dest_sem_value_T: typ -> typ
  val mk_sem_value_T: typ -> typ
end

structure Phi_Syntax : PHI_SYNTAX = struct
open Thm Term HOLogic Phi_Help Phi_Syntax

val dest_nuTy = dest_binop @{const_name "\<phi>Type"}
val dest_nuTy_c = dest_binop_c @{const_name "\<phi>Type"}
val mk_nuTy = mk_binop @{const_name "\<phi>Type"}
fun mk_Nu_ty (tya,tyb) = tyb --> Type(@{type_name Set.set}, [tya])

val dest_goal_ctxt   = dest_binop   \<^const_name>\<open>GOAL_CTXT\<close> #> #1
val dest_goal_ctxt_c = dest_binop_c \<^const_name>\<open>GOAL_CTXT\<close> #> #1

val dest_action_tag   = dest_binop   \<^const_name>\<open>Action_Tag\<close> #> #1
val dest_action_tag_c = dest_binop_c \<^const_name>\<open>Action_Tag\<close> #> #1


fun dest_tags X = X
  |> perhaps (try dest_goal_ctxt)
  |> perhaps (try dest_action_tag)
  |> perhaps (try dest_Trueprop)
fun dest_tags_c X = X
  |> perhaps (try dest_goal_ctxt_c)
  |> perhaps (try dest_action_tag_c)
  |> perhaps (try dest_Trueprop_c)


val dest_CurrentConstruction   =
      perhaps (try dest_Trueprop)   #> dest_quadop   @{const_name CurrentConstruction}
val dest_CurrentConstruction_c =
      perhaps (try dest_Trueprop_c) #> dest_quadop_c @{const_name CurrentConstruction}
val dest_PendingConstruction   =
      perhaps (try dest_Trueprop)   #> dest_quinop   @{const_name PendingConstruction}
val dest_PendingConstruction_c =
      perhaps (try dest_Trueprop_c) #> dest_quinop_c @{const_name PendingConstruction}
val dest_set_member   = dest_tags   #> dest_binop   @{const_name Set.member}
val dest_set_member_c = dest_tags_c #> dest_binop_c @{const_name Set.member}

fun is_construction_mode mode tm =
  case try dest_CurrentConstruction tm
    of SOME (m,_,_,_) => mode = m
     | _ => (case try dest_PendingConstruction tm
               of SOME (m,_,_,_,_) => mode = m
                | _ => false)

fun block_var_of_Constuction c   = (dest_CurrentConstruction c |> #2)
  handle TERM _ => ((dest_PendingConstruction c |> #2)
  handle TERM _ => raise TERM ("neithr CurrentConstruction nor PendingConstruction", [c]))
fun block_var_of_Constuction_c c = (dest_CurrentConstruction_c c |> #2)
  handle TERM _ => ((dest_PendingConstruction_c c |> #2)
  handle TERM _ => raise TERM ("neithr CurrentConstruction nor PendingConstruction", [term_of c]))

fun orelse_opt f1 f2 x = case f1 x of SOME y => y | NONE => f2 x
val dest_current_nu =
      Thm.prop_of #> perhaps (try dest_Trueprop)
        #> orelse_opt (try (dest_PendingConstruction #> #4)) (dest_CurrentConstruction #> #4)
val dest_current_nu_c =
      Thm.cprop_of #> perhaps (try dest_Trueprop_c)
        #> orelse_opt (try (dest_PendingConstruction_c #> #4)) (dest_CurrentConstruction_c #> #4)

val current_block_var_c =
  Thm.cprop_of
    #> perhaps (try strip_implies_c)
    #> perhaps (try dest_Trueprop_c)
    #> block_var_of_Constuction_c
val current_block_var =
  Thm.prop_of
    #> perhaps (try Logic.strip_assums_concl)
    #> perhaps (try dest_Trueprop)
    #> block_var_of_Constuction

val dest_procedure   =
     dest_tags
  #> dest_quadop @{const_name \<phi>Procedure}
val dest_procedure_c =
     dest_tags_c
  #> dest_quadop_c @{const_name \<phi>Procedure}

val dest_view_shift    =
         dest_tags
      #> dest_triop @{const_name View_Shift}
val dest_view_shift_c  =
         dest_tags_c
      #> dest_triop_c @{const_name View_Shift}

val dest_implication   =
         dest_tags
      #> dest_triop @{const_name "Imply"}
val dest_implication_c =
         dest_tags_c
      #> dest_triop_c @{const_name "Imply"}

val dest_Set_member =
         dest_tags
      #> dest_binop @{const_name "Set.member"}
val dest_Set_member_c =
         dest_tags_c
      #> dest_binop_c @{const_name "Set.member"}


fun dest_destined_phityp term =
  case try dest_procedure term
    of SOME (_,_,ty,_) => ty | _ => 
  case try dest_implication term
    of SOME (_,ty,_) => ty | _ => raise TERM ("dest_destined_phityp", [term])

fun dest_destined_phityp_c term =
  case try dest_procedure_c term
    of SOME (_,_,ty,_) => ty | _ => 
  case try dest_implication_c term
    of SOME (_,ty,_) => ty | _ => raise CTERM ("dest_destined_phityp", [term])


fun strip_separations (Const (@{const_name Subjection}, _) $ T) = strip_separations T
  | strip_separations (Const (@{const_name ExSet}, _) $ T) = strip_separations T
  | strip_separations (Abs (_, _, T)) = strip_separations T
  | strip_separations T = strip_binop_l @{const_name times} T

val dest_sem_value_T = dest_monop_ty \<^type_name>\<open>sem_value\<close>
fun mk_sem_value_T T = Type(\<^type_name>\<open>sem_value\<close>, [T])

end