(*  Title:      NuBasics.ML
    Author:     Qiyuan Xu

Basic supports for the nu-system.

*)
infix 0 MP MP_BY

signature NU_BASICS = sig
  exception NDBG of thm
  val repeat : ('a -> 'a) -> 'a -> 'a
  val ntimes : int -> (int -> 'a -> 'a) -> 'a -> 'a

  val nu_bind_name : string
  val the_nu_fact : Proof.state -> thm
  val set_nu_fact : thm -> Proof.state -> Proof.state

  val void_ty : typ
  val mk_stateT : typ -> typ
  val dest_tynuset_c : ctyp -> ctyp
  val dest_typroc_c : ctyp -> ctyp * ctyp

  val dest_param : term -> term
  val param_type : thm -> typ
  val dest_RepSet : term -> term * term
  val dest_RepSet_c : cterm -> cterm * cterm
  val mk_RepSet : term * term -> term
  val dest_nuTy : term -> term * term
  val dest_nuTy_c : cterm -> cterm * cterm
  val mk_nuTy : term * term -> term
  val mk_Nu_ty : typ * typ -> typ
  val dest_labelled_opt : term -> string option * term (* Labelled name, x -> (name,x) *)
  val label_ty : typ
  val label_cty : ctyp
  val dest_label : term -> string
  val mk_label : string -> term
  val mk_label_c : string -> cterm
  val mk_labelled : string -> term -> term
  val mk_name_hint : string -> term -> term
  val mk_repset : term -> term
  val mk_auto_tag : term -> term
  val dest_name_tylabels : typ -> string list (* 'i \<times> 'j \<times> 'k -> ["i","j","k"] *)
  val mk_name_tylabels : string list -> typ (* ["i","j","k"] -> 'i \<times> 'j \<times> 'k *)
  val dest_named : typ -> (string * typ) list
  val dest_named_only_names : typ -> (string * typ) list
  val normlize_name : string -> string
  val normlize_thm_of_names : thm -> thm

  (* val dest_andTy : term -> term * term *)
  val dest_CurrentConstruction : term -> term * term * term
  val dest_CurrentConstruction_c : cterm -> cterm * cterm * cterm
  val dest_PendingConstruction : term -> term * term * term * term
  val dest_PendingConstruction_c : cterm -> cterm * cterm * cterm * cterm
  val dest_current_nu   : thm -> term
  val dest_current_nu_c : thm -> cterm
  val dest_topctx'   : term -> (term list (* stack *) * term list (* heap *))
  val block_var_of_Constuction : term  -> term
  val block_var_of_Constuction_c : cterm  -> cterm
  val current_block_var   : thm -> term
  val current_block_var_c : thm -> cterm
  val current_block_depth : thm -> int
  val dest_codeblock   : term -> term * term * term
  val dest_codeblock_c : cterm -> cterm * cterm * cterm
  val codeblock_name   : term -> string
  val codeblocks_of   : thm -> term list
  val codeblocks_of_c : thm -> cterm list
  val current_codeblock : thm -> cterm

  val dest_procedure   : term -> term * term * term
  val dest_procedure_c : cterm -> cterm * cterm * cterm
  val dest_premise_tag  : term -> term * term
  val dest_premise_tag_c: cterm -> cterm * cterm

  val mk_PropBlock : int -> thm -> thm

  val dest_Cast   : term -> term * term * term
  val dest_Cast_c : cterm -> cterm * cterm * cterm

  val intro_param : cterm -> thm
  val intro_param_name : string -> thm

  val default_ty_R : typ
  val tail_stack_ty : typ -> typ -> typ

  val param_set_free_var_name : Proof.context -> string -> thm -> thm
  (* val auto_fusion_arity : term -> int *)

  val parse_arg_list : bool (*void tail*) -> term -> term
end
structure NuBasics = struct
open Thm Term HOLogic NuHelp
exception NDBG of thm

val nu_bind_name = "\<nu>this"
fun the_nu_fact stat = Proof_Context.get_thm (Proof.context_of stat) nu_bind_name
fun set_nu_fact th stat = stat
  |> Proof.set_facts [th]
  |> Proof.map_context (Proof_Context.put_thms false (nu_bind_name, SOME [th]));

fun repeat f x = repeat f (f x) handle TERM _ => x | THM _ => x
fun ntimes_i i n f x = if i < n then ntimes_i (i+1) n f (f i x) else x
fun ntimes n f x = ntimes_i 0 n f x
val void_ty = Type(@{type_name "void"}, [])
fun mk_stateT ty = Type(@{type_name "state"}, [ty])
(* \<alpha> set *)
val dest_tynuset_c = dest_ctyp0
(* heap \<times> \<alpha> |--> \<beta> set *)
fun dest_typroc_c ty = (dest_ctyp1 (dest_ctyp0 ty), dest_ctyp0 (dest_ctyp1 ty))

val thm_PropBlock_I = @{thm NuPrime.PropBlock_I}
fun mk_PropBlock n th = Drule.comp_no_flatten (th, n) 1 thm_PropBlock_I

fun catch msg f tm = (f tm) handle TERM _ => raise TERM (msg, [tm])
fun catch_th i msg f th = (f th) handle THM _ => raise THM (msg, i, [th])
                                    | TERM _ => raise TERM (msg, [prop_of th])

val dest_param = perhaps (try dest_Trueprop) #> dest_monop @{const_name "ParamTag"}
val dest_param_c = dest_monop_c @{const_name "ParamTag"}
fun param_type_c th = cprem_of th 1 |> dest_param_c |> ctyp_of_cterm
fun param_type th = major_prem_of th |> dest_param |> type_of
val unit_const_name = @{const_name "Product_Type.Unity"}
val label_ty = Type (@{type_name "label"}, [])
val label_cty = @{ctyp "label"}
val label_const_name = @{const_name "LABEL_TAG"}
val unit_ty = Type (@{type_name "Product_Type.unit"}, [])
val unit_const = Const("Product_Type.Unity", unit_ty)
val label_const = Const (label_const_name, (unit_ty --> unit_ty) --> label_ty)
val dest_label_raw   = dest_monop label_const_name
val dest_label_raw_c = dest_monop_c label_const_name
fun dest_Abs (Abs x) =  x
  | dest_Abs t = raise TERM("dest_Abs", [t]);
fun dest_label tm =
  tm |> Type.strip_constraints |> dest_label_raw |> dest_Abs |> #1
    handle TERM _ => raise TERM ("dest_label", [tm])
val label_c = @{cterm "LABEL name"}
fun mk_label name = label_const $ Abs (name, unit_ty, unit_const)
fun mk_label_c name = renamed_term (mk_label name) label_c
fun mk_label_thm name = 
  Thm.instantiate ([],[((("x",0),@{typ label}), mk_label_c name)]) @{thm LabelTag}
fun mk_labelled name tm = Const(@{const_name Labelled}, dummyT) $ mk_label name $ tm
fun mk_name_hint name tm = Const(@{const_name NameHint}, dummyT) $ mk_label name $ tm

val labelled_name = @{const_name "Labelled"}
val dest_labelled = dest_binop labelled_name #> apfst dest_label
fun dest_labelled_opt tm =
  case try (dest_binop labelled_name) tm of
     SOME (v,tm) => (SOME (dest_label v), tm)
   | NONE => (NONE, tm)
fun mk_repset (tm as (Const (@{const_name "RepSet"}, _) $ _)) = tm
  | mk_repset tm = mk_monop @{const_name "RepSet"} tm
val nuTy_name = @{const_name "typing"}
val dest_nuTy = dest_binop nuTy_name
val dest_nuTy_c = dest_binop_c nuTy_name
val dest_RepSet = dest_monop @{const_name "RepSet"} #> dest_nuTy
val dest_RepSet_c = dest_monop_c @{const_name "RepSet"} #> dest_nuTy_c
val mk_nuTy = mk_binop nuTy_name
val mk_RepSet = mk_nuTy #> mk_monop @{const_name "RepSet"}
fun mk_Nu_ty (tya,tyb) = tyb --> Type(@{type_name Set.set}, [tya])
(* fun dest_andTy (Const (@{const_name "AndTy"}, _) $ t1 $ t2) = (t1, t2)
  | dest_andTy t = raise TERM ("bad AndTy", [t]); *)
val mk_auto_tag = mk_monop @{const_name "Auto"}

val dest_CurrentConstruction   =
      perhaps (try dest_Trueprop) #> dest_triop @{const_name "CurrentConstruction"}
val dest_CurrentConstruction_c =
      perhaps (try dest_Trueprop_c) #> dest_triop_c @{const_name "CurrentConstruction"}
val dest_PendingConstruction   =
      perhaps (try dest_Trueprop) #> dest_quadop @{const_name "PendingConstruction"}
val dest_PendingConstruction_c =
      perhaps (try dest_Trueprop_c) #> dest_quadop_c @{const_name "PendingConstruction"}

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

val dest_topctx = dest_binop @{const_name "NuTopCtx"}
val dest_topctx_c = dest_binop_c @{const_name "NuTopCtx"}

fun dest_topctx' tm = dest_topctx tm
      |> apfst (strip_binop_l @{const_name Stack_Delimiter})
      |> apsnd (strip_binop_l @{const_name Heap_Divider})

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
val dest_codeblock   = perhaps (try dest_Trueprop) #> dest_triop @{const_name "NuPrime.CodeBlock"}
val codeblock_name   = dest_codeblock #> #1 #> term_name
val dest_codeblock_c = perhaps (try dest_Trueprop_c) #> dest_triop_c @{const_name "NuPrime.CodeBlock"}
val codeblocks_of   = hyps_of  #> filter (can dest_codeblock  )
val codeblocks_of_c = chyps_of #> filter (can dest_codeblock_c)
fun current_block_depth th =
  codeblocks_of th |> filter (dest_codeblock #> #1 #> term_name #>
    (String.isPrefix "\<nu>hide_") #> not) |> length
fun current_codeblock specthm =
  let
    val blk_var = current_block_var specthm
  in
    chyps_of specthm
  |> find_first (fn hy => (term_of hy |> try (dest_codeblock #> #1)) = SOME blk_var)
  |> Option.valOf
  end
fun disch_codeblock cb th =
  implies_intr cb th |> forall_intr (dest_codeblock_c cb |> #1)
fun undisch_codeblock cb_var = Thm.forall_elim cb_var #> undisch
fun disch_current_codeblock specthm =
  disch_codeblock (current_codeblock specthm) specthm


fun th1 MP th2 = Drule.comp_no_flatten (th1, 0) 1 th2
fun rule MP_BY args = fold (fn arg => fn rule => arg MP rule) args rule


val thm_ParamTag = @{thm ParamTag}
fun param_set_free_var_name ctx name thm =
  let
    val param_var as (_, param_ty) = prems_of thm |> hd |> dest_param |> dest_Var
  in
    instantiate ([], [(param_var, cterm_of ctx (Free (name, param_ty)))]) thm
      |> (fn x => thm_ParamTag RS x)
  end

val dest_procedure   = perhaps (try dest_Trueprop)
  (* #> strip_binder @{const_name All} #> #2
  #> strip_binop_r @{const_name HOL.implies} #> last *)
  #> dest_triop @{const_name "Procedure"}
val dest_procedure_c = perhaps (try dest_Trueprop_c)
  (* #> strip_binder_c @{const_name All} #> #2
  #> strip_binop_r_c @{const_name HOL.implies} #> last *)
  #> dest_triop_c @{const_name "Procedure"}
val dest_premise_tag  = dest_binop   @{const_name "Premise"} o perhaps (try dest_Trueprop)
val dest_premise_tag_c= dest_binop_c @{const_name "Premise"} o perhaps (try dest_Trueprop_c)

val vx = ("x",0) and va = ("'a",0)
fun intro_param tm =
  Thm.instantiate ([((("'a",0), ["HOL.type"]), ctyp_of_cterm tm)],
                   [((("x",0), typ_of (ctyp_of_cterm tm)), tm)]) @{thm ParamTag}
val intro_param_name = intro_param o mk_label_c

val dest_Cast   = dest_triop   @{const_name "Cast"}
val dest_Cast_c = dest_triop_c @{const_name "Cast"}


fun trim_tylabel_name name = String.substring(name, 2, size name - 2)
fun dest_name_tylabel (TFree (name,_)) = trim_tylabel_name name
  | dest_name_tylabel (TVar ((name,_),_)) = trim_tylabel_name name
val dest_name_tylabels = HOLogic.strip_tupleT #> map dest_name_tylabel
fun mk_name_tylabels names = HOLogic.mk_tupleT (map (fn x => TFree ("'_"^x, ["HOL.type"])) names)
fun dest_named (Type (@{type_name named}, [tys, names]))
      = dest_name_tylabels names ~~ HOLogic.strip_tupleT tys
  | dest_named ty = raise TYPE ("dest_named", [ty], [])
fun dest_named_only_names (Type (@{type_name named}, [_, names]))
      = dest_name_tylabels names
  | dest_named_only_names ty = raise TYPE ("dest_named", [ty], [])

fun normlize_name name =
  if String.isSuffix "__" name then String.substring (name,0, size name - 2)
  else name
fun normlize_thm_of_names th =
  let
    val thy = Thm.theory_of_thm th
    val insts = Thm.add_tvars th []
                  |> map_filter (fn x => case typ_of x of TVar (tvar as ((name,_),["HOL.type"])) =>
                      if String.isPrefix "'_" name
                      then SOME (tvar, Thm.global_ctyp_of thy (TFree (name,["HOL.type"])))
                      else NONE
                                            | _ => NONE)
  in
    Thm.instantiate (insts,[]) th
  end

(* val auto_fusion_arity =
  Logic.strip_assums_concl #> perhaps (try dest_Trueprop) #> perhaps_try (dest_procedure #> #2)
  #> perhaps_try (dest_binop "NuPrime.Stack_Delimiter" #> #2)
  #> perhaps (try dest_RepSet) #> perhaps_try (dest_nuTy #> #2)
  #> repeat (dest_binop "NuBasicAbstractors.NuRefine" #> #1)
  #> repeat (dest_binop "NuBasicAbstractors.SchemaCondition" #> #1)
  #> repeat (dest_binop "NuBasicAbstractors.Schema" #> #1)
  #> strip_binop_r "NuLLReps.AutoFusion" #> length *)

(*default type remander*)
val default_ty_R = TFree ("'\<RR>", [@{class "stack"}])
(*translate tail of a stack type to `ty_R`, if it ends with void*)
fun tail_stack_ty ty_R (Type (@{type_name prod}, [a, b])) =
      Type (@{type_name prod}, [a, tail_stack_ty ty_R a])
  | tail_stack_ty ty_R (Type (@{type_name void}, _)) = ty_R
  | tail_stack_ty ty_R ty = ty

local
fun is_free_var' tm = is_Free tm orelse is_Var tm
fun is_free_var tm = is_free_var' (Type.strip_constraints tm)
in

fun tr_stack void_tail (Const (@{const_name Stack_Delimiter},_) $ A $ B)
      = Const (@{const_name Stack_Delimiter},dummyT) $ tr_stack void_tail A $ B
  | tr_stack void_tail (tm as (Const (@{const_name RepSet},_) $ _))
      = Const (@{const_name Stack_Delimiter},dummyT)
          $ (if void_tail then @{term Void} else Free ("\<RR>", dummyT)) $ tm
  | tr_stack void_tail (Const ("_type_constraint_", ty) $ tm)
      = Const ("_type_constraint_", ty) $ tr_stack void_tail tm
  | tr_stack _ tm = tm

fun tr_heap (Const (@{const_name Heap_Divider},_) $ A $ B)
      = Const (@{const_name Heap_Divider},dummyT) $ tr_heap A $ B
  | tr_heap (tm as (Const (@{const_name RepSet},_) $ _))
      = Const (@{const_name Heap_Divider},dummyT)
          $ Free ("\<HH>", dummyT) $ tm
  | tr_heap (Const ("_type_constraint_", ty) $ tm)
      = Const ("_type_constraint_", ty) $ tr_heap tm
  | tr_heap tm = tm

fun tr_topctx void_tail (Const (@{const_name NuTopCtx},_) $ S $ H)
      = Const (@{const_name NuTopCtx}, dummyT) $ tr_stack void_tail S $ H
  | tr_topctx void_tail (tm as (Const (@{const_name Front_Stack},_) $ _ $ _))
      = tm
  | tr_topctx void_tail (Abs (name, _, body))
      = Abs (name, dummyT, tr_topctx void_tail body)
  | tr_topctx void_tail (Const (@{const_name ExSet}, _) $ body)
      = Const (@{const_name ExSet}, dummyT) $ tr_topctx void_tail body
  | tr_topctx void_tail (Const (@{const_name Subjection}, _) $ body $ P)
      = Const (@{const_name Subjection}, dummyT) $ tr_topctx void_tail body $ P
  | tr_topctx void_tail (Const ("_type_constraint_", ty) $ tm)
      = Const ("_type_constraint_", ty) $ tr_topctx void_tail tm
  | tr_topctx void_tail (tm as (Const (@{const_name Stack_Delimiter}, _) $ A $ B))
      = Const (@{const_name NuTopCtx},dummyT) $ tr_stack void_tail tm
          $ @{term Nothing}
  | tr_topctx void_tail (tm as (Const (@{const_name typing},_) $ _ $ _))
      = Const (@{const_name NuTopCtx},dummyT)
          $ tr_stack void_tail (mk_monop @{const_name RepSet} tm)
          $ @{term Nothing}
  | tr_topctx void_tail (tm as (Const (@{const_name RepSet},_) $ _))
      = Const (@{const_name NuTopCtx},dummyT)
          $ tr_stack void_tail tm
          $ @{term Nothing}
  | tr_topctx void_tail tm = tm

val parse_arg_list = tr_topctx

end
end
