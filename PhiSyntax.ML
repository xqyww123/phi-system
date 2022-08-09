signature PHI_SYNTAX = sig
include PHI_SYNTAX

  val get_types : Proof.context ->
        {TY_N: typ, TY: typ, VAL_N: typ, VAL: typ, RES_N: typ, RES: typ, FIC_N: typ, FIC: typ}
  val get_assn_typ : Proof.context -> typ

  val mk_stateT : Proof.context -> typ -> typ
  val mk_resourceT : Proof.context -> typ
  val mk_assnT : Proof.context -> typ
  val mk_procT : Proof.context -> typ -> typ

  val dest_nuTy : term -> term * term
  val dest_nuTy_c : cterm -> cterm * cterm
  val mk_nuTy : term * term -> term
  val mk_Nu_ty : typ * typ -> typ

  val dest_CurrentConstruction : term -> term * term * term
  val dest_CurrentConstruction_c : cterm -> cterm * cterm * cterm
  val dest_PendingConstruction : term -> term * term * term * term * term
  val dest_PendingConstruction_c : cterm -> cterm * cterm * cterm * cterm * cterm
  val dest_current_nu   : thm -> term
  val dest_current_nu_c : thm -> cterm

  val block_var_of_Constuction : term  -> term
  val block_var_of_Constuction_c : cterm  -> cterm
  val current_block_var   : thm -> term
  val current_block_var_c : thm -> cterm

  val dest_procedure   : term -> term * term * term * term
  val dest_procedure_c : cterm -> cterm * cterm * cterm * cterm

  val dest_destined_phityp   : term -> term
  val dest_destined_phityp_c : cterm -> cterm

  val dest_subtyping   : term  -> term * term * term
  val dest_subtyping_c : cterm -> cterm * cterm * cterm

  val strip_separations : term -> term list

  val dest_sem_value_T: typ -> typ
  val mk_sem_value_T: typ -> typ
end

structure PhiSyntax : PHI_SYNTAX = struct
open Thm Term HOLogic NuHelp PhiSyntax

fun get_types ctxt =
  let
    val SOME tys = Variable.default_type ctxt "TYPES"
    val Type ("itself", [
          Type (@{type_name prod}, [Type("fun", [TY_N, TY]),
            Type (@{type_name prod}, [Type("fun", [VAL_N, VAL]),
              Type (@{type_name prod}, [Type("fun", [RES_N, RES]),
                Type("fun", [FIC_N, FIC])])])])])
        = tys
  in
    {TY_N=TY_N, TY=TY, VAL_N=VAL_N, VAL=VAL, RES_N=RES_N, RES=RES, FIC_N=FIC_N, FIC=FIC}
  end
  handle BIND => error ("Corrupted TYPES entry!")

fun get_assn_typ ctxt =
  let val {FIC_N,FIC,...} = get_types ctxt
   in Type (\<^type_name>\<open>set\<close>, [Type("fun", [FIC_N, FIC])]) end


fun mk_stateT ctxt T =
  let
    val {RES_N,RES,...} = get_types ctxt
  in
    Type(@{type_name "state"}, [T,RES_N,RES])
  end

fun mk_resourceT ctxt =
  let
    val {RES_N,RES,...} = get_types ctxt
  in
    Type(@{type_name "fun"}, [RES_N, RES])
  end

fun mk_assnT ctxt =
  let
    val {FIC_N,FIC,...} = get_types ctxt
  in
    Type(@{type_abbrev "assn"}, [FIC_N,FIC])
  end

fun mk_procT ctxt T =
  let
    val {VAL,RES_N,RES,...} = get_types ctxt
  in
    Type(@{type_abbrev "proc"}, [T,RES_N,RES])
  end


fun catch msg f tm = (f tm) handle TERM _ => raise TERM (msg, [tm])
fun catch_th i msg f th = (f th) handle THM _ => raise THM (msg, i, [th])
                                      | TERM _ => raise TERM (msg, [prop_of th])


val dest_nuTy = dest_binop @{const_name "\<phi>Type"}
val dest_nuTy_c = dest_binop_c @{const_name "\<phi>Type"}
val mk_nuTy = mk_binop @{const_name "\<phi>Type"}
fun mk_Nu_ty (tya,tyb) = tyb --> Type(@{type_name Set.set}, [tya])

val dest_CurrentConstruction   =
      perhaps (try dest_Trueprop) #> dest_triop @{const_name "\<phi>empty.CurrentConstruction"}
val dest_CurrentConstruction_c =
      perhaps (try dest_Trueprop_c) #> dest_triop_c @{const_name "\<phi>empty.CurrentConstruction"}
val dest_PendingConstruction   =
      perhaps (try dest_Trueprop) #> dest_quinop @{const_name "\<phi>empty.PendingConstruction"}
val dest_PendingConstruction_c =
      perhaps (try dest_Trueprop_c) #> dest_quinop_c @{const_name "\<phi>empty.PendingConstruction"}

fun block_var_of_Constuction c   = (dest_CurrentConstruction c |> #1)
  handle TERM _ => ((dest_PendingConstruction c |> #2)
  handle TERM _ => raise TERM ("neithr CurrentConstruction nor PendingConstruction", [c]))
fun block_var_of_Constuction_c c = (dest_CurrentConstruction_c c |> #1)
  handle TERM _ => ((dest_PendingConstruction_c c |> #2)
  handle TERM _ => raise TERM ("neithr CurrentConstruction nor PendingConstruction", [term_of c]))

fun orelse_opt f1 f2 x = case f1 x of SOME y => y | NONE => f2 x
val dest_current_nu =
      Thm.prop_of #> perhaps (try dest_Trueprop)
        #> orelse_opt (try (dest_PendingConstruction #> #4)) (dest_CurrentConstruction #> #3)
val dest_current_nu_c =
      Thm.cprop_of #> perhaps (try dest_Trueprop_c)
        #> orelse_opt (try (dest_PendingConstruction_c #> #4)) (dest_CurrentConstruction_c #> #3)

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

val dest_goal_ctxt   = dest_binop   \<^const_name>\<open>GOAL_CTXT\<close> #> #1
val dest_goal_ctxt_c = dest_binop_c \<^const_name>\<open>GOAL_CTXT\<close> #> #1

val dest_procedure   = perhaps (try dest_Trueprop) #> perhaps (try dest_goal_ctxt)
  #> dest_quadop @{const_name "\<phi>empty.\<phi>Procedure"}
val dest_procedure_c = perhaps (try dest_Trueprop_c) #> perhaps (try dest_goal_ctxt_c)
  #> dest_quadop_c @{const_name "\<phi>empty.\<phi>Procedure"}

val dest_subtyping   =
         perhaps (try dest_Trueprop)
      #> perhaps (try dest_goal_ctxt)
      #> dest_triop @{const_name "Subty"}
val dest_subtyping_c =
         perhaps (try dest_Trueprop_c)
      #> perhaps (try dest_goal_ctxt_c)
      #> dest_triop_c @{const_name "Subty"}


fun dest_destined_phityp term =
  case try dest_procedure term
    of SOME (_,_,ty,_) => ty | _ => 
  case try dest_subtyping term
    of SOME (_,ty,_) => ty | _ => raise TERM ("dest_destined_phityp", [term])

fun dest_destined_phityp_c term =
  case try dest_procedure_c term
    of SOME (_,_,ty,_) => ty | _ => 
  case try dest_subtyping_c term
    of SOME (_,ty,_) => ty | _ => raise CTERM ("dest_destined_phityp", [term])


fun strip_separations (Const (@{const_name Subjection}, _) $ T) = strip_separations T
  | strip_separations (Const (@{const_name ExSet}, _) $ T) = strip_separations T
  | strip_separations (Abs (_, _, T)) = strip_separations T
  | strip_separations T = strip_binop_l @{const_name times} T

val dest_sem_value_T = dest_monop_ty \<^type_name>\<open>sem_value\<close>
fun mk_sem_value_T T = Type(\<^type_name>\<open>sem_value\<close>, [T])

end
