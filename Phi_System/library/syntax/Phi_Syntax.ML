signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val assn_fictionT : typ
  val is_procT  : typ -> bool
  val dest_procT_params : typ -> typ list
  val mk_procT  : typ -> typ
  val mk_proc'T : typ -> typ -> typ

  val is_construction_mode: term -> term -> bool
  val dest_CurrentConstruction   :  term -> term * term * term * term
  val dest_CurrentConstruction_c : cterm -> cterm * cterm * cterm * cterm
  val dest_PendingConstruction : term -> term * term * term * term * term
  val dest_PendingConstruction_c : cterm -> cterm * cterm * cterm * cterm * cterm
  val pending_construction_monad_conv : conv -> conv
  val pending_construction_abnm_conv : conv -> conv

  val block_var_of_Constuction : term  -> term
  val block_var_of_Constuction_c : cterm  -> cterm
  val current_block_var   : thm -> term
  val current_block_var_c : thm -> cterm

  val dest_ToA_Construction    : term  -> term * term
  val dest_ToA_Construction_c  : cterm -> cterm * cterm

  val dest_CodeBlock   : term -> term * term * term * term
  val dest_CodeBlock_c : cterm -> cterm * cterm * cterm * cterm

  val dest_satisfaction : term -> term * term
  val dest_satisfaction_c : cterm -> cterm * cterm

  val dest_target_assertion : term -> term


  (*for statistics*)
  val semantic_oprs : int Symtab.table Synchronized.var
  val semantic_operations : term -> (string * int) list (*may not be accurate*)
  val count_semantic_operations : term -> int

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Thm Term HOLogic Phi_Help Phi_Syntax

fun is_procT (\<^Type>\<open>fun \<^Type>\<open>fun \<^Type>\<open>RES_N\<close> \<^Type>\<open>RES\<close>\<close> \<^Type>\<open>set \<^Type>\<open>comp \<open>_\<close>\<close>\<close>\<close>) = true
  | is_procT (\<^Type>\<open>fun _ T\<close>) = is_procT T
  | is_procT _ = false
fun dest_procT_params (\<^Type>\<open>fun \<^Type>\<open>fun \<^Type>\<open>RES_N\<close> \<^Type>\<open>RES\<close>\<close> \<^Type>\<open>set \<^Type>\<open>comp \<open>_\<close>\<close>\<close>\<close>) = []
  | dest_procT_params (\<^Type>\<open>fun a T\<close>) = a :: dest_procT_params T
  | dest_procT_params t = raise TYPE("not a procedure", [t], [])

fun mk_procT T = \<^typ>\<open>resource\<close> --> \<^Type>\<open>set \<open>\<^Type>\<open>comp T\<close>\<close>\<close>
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

fun pending_construction_monad_conv C =
  Phi_Conv.tag_conv (fn ctm =>
    case Thm.term_of ctm
      of (Const (\<^const_name>\<open>PendingConstruction\<close>, _) $ _ $ _ $ _ $ _ $ _)
           => Conv.fun_conv (Conv.fun_conv (Conv.fun_conv (Conv.fun_conv (Conv.arg_conv C)))) ctm
       | _ => raise CTERM ("pending_construction_monad_conv", [ctm])
     )
fun pending_construction_abnm_conv C =
  Phi_Conv.tag_conv (fn ctm =>
    case Thm.term_of ctm
      of (Const (\<^const_name>\<open>PendingConstruction\<close>, _) $ _ $ _ $ _ $ _ $ _)
           => (Conv.arg_conv C) ctm
       | _ => raise CTERM ("pending_construction_abnm_conv", [ctm])
     )

val dest_CodeBlock   = perhaps (try dest_Trueprop)   #> dest_quadop   \<^const_name>\<open>CodeBlock\<close>
val dest_CodeBlock_c = perhaps (try dest_Trueprop_c) #> dest_quadop_c \<^const_name>\<open>CodeBlock\<close>

fun is_construction_mode mode tm =
  case try dest_CurrentConstruction tm
    of SOME (m,_,_,_) => mode = m
     | _ => mode = \<^const>\<open>programming_mode\<close> andalso can dest_PendingConstruction tm

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
         PLPR_Syntax.dest_tags
      #> dest_binop   @{const_name ToA_Construction}
val dest_ToA_Construction_c =
         PLPR_Syntax.dest_tags_c
      #> dest_binop_c @{const_name ToA_Construction}

val dest_satisfaction =
      PLPR_Syntax.dest_tags #> dest_binop \<^const_name>\<open>Satisfaction\<close>
fun dest_satisfaction_c ctm = ctm
      |> PLPR_Syntax.dest_tags_c
      |> dest_binop_c \<^const_name>\<open>Satisfaction\<close>

fun dest_target_assertion' (Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ X $ _) = X
  | dest_target_assertion' (Const(\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ _ $ X $ _ ) = X
  | dest_target_assertion' (Const(\<^const_name>\<open>View_Shift\<close>, _) $ _ $ X $ _ ) = X
  | dest_target_assertion' (Const(\<^const_name>\<open>ToA_Construction\<close>, _) $ _ $ X ) = X
  | dest_target_assertion' (Const(\<^const_name>\<open>PendingConstruction\<close>, _) $ _ $ _ $ _ $ X $ _) = X
  | dest_target_assertion' (Const(\<^const_name>\<open>CurrentConstruction\<close>, _) $ _ $ _ $ _ $ X ) = X
  | dest_target_assertion' X = raise TERM ("dest_target_assertion", [X])

val dest_target_assertion = dest_target_assertion' o PLPR_Syntax.dest_tags o Logic.strip_assums_concl

val semantic_oprs = Synchronized.var "semantic_oprs" Symtab.empty
fun semantic_operations (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = semantic_operations X
  | semantic_operations (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ X) = semantic_operations X
  | semantic_operations (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ X) = semantic_operations X
  | semantic_operations term =
      let val soprs = Synchronized.value semantic_oprs
       in Phi_Help.fold_aterms
            (fn bvs => (fn Const(\<^const_name>\<open>bind\<close>, _) => I
                         | Const(\<^const_name>\<open>Return\<close>, _) => I
                         | Const(\<^const_name>\<open>Nondet\<close>, _) => I
                         | Const(\<^const_name>\<open>\<phi>V_case_prod\<close>, _) => I
                         | Const(N, T) => (fn L =>
                              case Symtab.lookup soprs N
                                of SOME w => if 0 < w then (N,w) :: L else L
                                 | _ => if is_procT T then (N,1) :: L else L)
                         | Free (N, T) => (fn L => if is_procT T then (N,1) :: L else L)
                         | Bound i => (fn L => case nth bvs i of (N,T) => if is_procT T then (N,1) :: L else L)
                         | _ => I)) [] term []
      end

fun count_semantic_operations term =
      Integer.sum (map #2 (semantic_operations term)) + 1

end
