signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val assn_fictionT : typ
  val mk_procT  : typ -> typ
  val mk_proc'T : typ -> typ -> typ

  val is_construction_mode: term -> term -> bool
  val dest_CurrentConstruction   :  term -> term * term * term * term
  val dest_CurrentConstruction_c : cterm -> cterm * cterm * cterm * cterm
  val dest_PendingConstruction : term -> term * term * term * term * term
  val dest_PendingConstruction_c : cterm -> cterm * cterm * cterm * cterm * cterm
  val pending_construction_monad_conv : conv -> conv
  val pending_construction_abnm_conv : conv -> conv
  val dest_set_member   :  term ->  term * term
  val dest_set_member_c : cterm -> cterm * cterm

  val block_var_of_Constuction : term  -> term
  val block_var_of_Constuction_c : cterm  -> cterm
  val current_block_var   : thm -> term
  val current_block_var_c : thm -> cterm

  val dest_ToA_Construction    : term  -> term * term
  val dest_ToA_Construction_c  : cterm -> cterm * cterm

  val dest_CodeBlock   : term -> term * term * term * term
  val dest_CodeBlock_c : cterm -> cterm * cterm * cterm * cterm

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Thm Term HOLogic Phi_Help Phi_Syntax

fun mk_procT T = \<^typ>\<open>resource\<close> --> \<^Type>\<open>set \<open>\<^Type>\<open>state T\<close>\<close>\<close>
fun mk_proc'T T U = \<^Type>\<open>\<phi>arg T\<close> --> mk_procT U
val assn_fictionT = \<^typ>\<open>assn\<close>

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

fun pending_construction_monad_conv C =
  Phi_Helper_Conv.may_action_tag_conv (Phi_Helper_Conv.may_Trueprop_conv (fn ctm =>
    case Thm.term_of ctm
      of (Const (\<^const_name>\<open>PendingConstruction\<close>, _) $ _ $ _ $ _ $ _ $ _)
           => Conv.fun_conv (Conv.fun_conv (Conv.fun_conv (Conv.fun_conv (Conv.arg_conv C)))) ctm
       | _ => raise CTERM ("pending_construction_monad_conv", [ctm])
     ))
fun pending_construction_abnm_conv C =
  Phi_Helper_Conv.may_action_tag_conv (Phi_Helper_Conv.may_Trueprop_conv (fn ctm =>
    case Thm.term_of ctm
      of (Const (\<^const_name>\<open>PendingConstruction\<close>, _) $ _ $ _ $ _ $ _ $ _)
           => (Conv.arg_conv C) ctm
       | _ => raise CTERM ("pending_construction_abnm_conv", [ctm])
     ))

val dest_CodeBlock   = perhaps (try dest_Trueprop)   #> dest_quadop   \<^const_name>\<open>CodeBlock\<close>
val dest_CodeBlock_c = perhaps (try dest_Trueprop_c) #> dest_quadop_c \<^const_name>\<open>CodeBlock\<close>

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

val dest_ToA_Construction =
         dest_tags
      #> dest_binop   @{const_name ToA_Construction}
val dest_ToA_Construction_c =
         dest_tags_c
      #> dest_binop_c @{const_name ToA_Construction}

end
