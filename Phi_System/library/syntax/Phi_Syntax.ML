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

  val block_var_of_Constuction : term  -> term
  val block_var_of_Constuction_c : cterm  -> cterm
  val current_block_var   : thm -> term
  val current_block_var_c : thm -> cterm

  val dest_ToA_Construction    : term  -> term * term
  val dest_ToA_Construction_c  : cterm -> cterm * cterm

  val dest_CodeBlock   : term -> term * term * term * term
  val dest_CodeBlock_c : cterm -> cterm * cterm * cterm * cterm

  val dest_satisfaction : term -> term * term

  val is_BI_connective : term -> bool
  val fold_items_of_assertion : (term -> 'a -> 'a) -> term -> 'a -> 'a
  val exists_item_of_assertion : (term -> bool) -> term -> bool
  val forall_item_of_assertion : (term -> bool) -> term -> bool

end

structure Phi_Syntax : PHI_SYNTAX = struct
open Thm Term HOLogic Phi_Help Phi_Syntax

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
         dest_tags
      #> dest_binop   @{const_name ToA_Construction}
val dest_ToA_Construction_c =
         dest_tags_c
      #> dest_binop_c @{const_name ToA_Construction}

val dest_satisfaction =
      dest_tags #> dest_binop \<^const_name>\<open>Satisfaction\<close>

fun is_BI_connective (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>)) = true
  | is_BI_connective (Const(\<^const_name>\<open>Subjection\<close>, _)) = true
  | is_BI_connective (Const(\<^const_name>\<open>ExSet\<close>, _)) = true
  | is_BI_connective (Const(\<^const_name>\<open>\<phi>Type\<close>, _)) = true
  | is_BI_connective (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>)) = true
  | is_BI_connective (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) = true
  | is_BI_connective (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) = true
  | is_BI_connective (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) = true
  | is_BI_connective (Const(\<^const_name>\<open>Additive_Conj\<close>, _)) = true
  | is_BI_connective (Const(\<^const_name>\<open>FOCUS_TAG\<close>, _)) = true
  | is_BI_connective (A $ _) = is_BI_connective A
  | is_BI_connective _ = false

(*including all \<phi>-type terms and atomic predicates*)
fun fold_items_of_assertion f =
  let fun fold (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) x = fold A (fold B x)
        | fold (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) x = fold X x
        | fold (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) x = fold X x
        | fold (Abs (_, _, X)) x = fold X x
        | fold (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) x = f X x
        | fold (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>fun _ \<^Type>\<open>fun _ \<^Type>\<open>set _\<close>\<close>\<close>) $ A $ B) x = fold A (fold B x)
        | fold (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) x = x
        | fold (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) x = fold X x
        | fold (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) x = fold A (fold B x)
        | fold (Const(\<^const_name>\<open>FOCUS_TAG\<close>, _) $ X) x = fold X x
        | fold X x = f X x
   in fold
  end

fun exists_item_of_assertion P =
  let fun exists (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>set _\<close>) $ A $ B) = exists B orelse exists A
        | exists (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = exists X
        | exists (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = exists X
        | exists (Abs (_, _, X)) = exists X
        | exists (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) = P X
        | exists (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>set _\<close>) $ A $ B) = exists B orelse exists A
        | exists (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) = false
        | exists (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) = false
        | exists (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) = false
        | exists (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) = exists X
        | exists (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) = exists B orelse exists A
        | exists (Const(\<^const_name>\<open>FOCUS_TAG\<close>, _) $ X) = exists X
        | exists X = P X
   in exists
  end

fun forall_item_of_assertion P =
  let fun forall (Const(\<^const_name>\<open>times\<close>, \<^Type>\<open>set _\<close>) $ A $ B) = forall B orelse forall A
        | forall (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = forall X
        | forall (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) = forall X
        | forall (Abs (_, _, X)) = forall X
        | forall (X as (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _)) = P X
        | forall (Const(\<^const_name>\<open>plus\<close>, \<^Type>\<open>set _\<close>) $ A $ B) = forall B orelse forall A
        | forall (Const(\<^const_name>\<open>top\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall (Const(\<^const_name>\<open>bot\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall (Const(\<^const_name>\<open>zero_class.zero\<close>, \<^Type>\<open>set _\<close>)) = true
        | forall (Const(\<^const_name>\<open>AllSet\<close>, _) $ X) = forall X
        | forall (Const(\<^const_name>\<open>Additive_Conj\<close>, _) $ A $ B) = forall B orelse forall A
        | forall (Const(\<^const_name>\<open>FOCUS_TAG\<close>, _) $ X) = forall X
        | forall X = P X
   in forall
  end

end
