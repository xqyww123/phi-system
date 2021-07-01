(*  Title:      NuBasics.ML
    Author:     Qiyuan Xu

Basic supports for the nu-system.

*)
infix 0 MP MP_BY

signature NU_BASICS = sig
  val void_ty : typ
  val proc_ctx_ty : typ * typ -> typ
  val mk_stateT : typ -> typ

  val dest_param : term -> term
  val dest_nuTy : term -> term * term
  val dest_named : term -> string option * term (* Named name, x -> (name,x) *)
  val name_tag_ty : typ
  val dest_name_tag : term -> string
  val mk_name_tag : string -> term
  val dest_register : term -> string * term
  val dest_registerTy : term -> string * term
  val Void_name : string
  val dest_andTy : term -> term * term
  val dest_andTys : term -> (unit,term) BiTree.T
  val dest_registerTys : term -> (unit,string) BiTree.T option
  val dest_SpecTop   : term -> term * term
  val dest_SpecTop_c : cterm -> cterm * cterm
  val dest_CurrentConstruction : term -> term * term
  val dest_CurrentConstruction_c : cterm -> cterm * cterm
  val dest_PendingConstruction : term -> term * term * term
  val dest_PendingConstruction_c : cterm -> cterm * cterm * cterm
  val dest_Proc_CtxTy : term -> term * term
  val dest_Proc_CtxTy_c : cterm -> cterm * cterm
  val registers_of_specthm : thm -> cterm
  val block_var_of_Constuction : term  -> term
  val block_var_of_Constuction_c : cterm  -> cterm
  val state_of_specthm : thm -> term
  val premise_of_specthm : thm -> term
  val current_block_var : thm -> cterm
  val dest_codeblock   : term -> term * term * term * term
  val dest_codeblock_c : cterm -> cterm * cterm * cterm * cterm
  val codeblocks_of   : thm -> term list
  val codeblocks_of_c : thm -> term list
  val codeblock_name   : term -> term * term * term * term
  val current_codeblock : thm -> cterm
  val disch_current_codeblock : thm -> thm

  val dest_procedure   : term -> term * term * term
  val dest_procedure_c : cterm -> cterm * cterm * cterm

  val elim_SPEC : thm -> thm * thm
  val intro_SPEC : thm * thm -> thm
  val mk_PropBlock : int -> thm -> thm

  val dest_fact : term -> string * term
  val dest_fact_c : cterm -> string * cterm
  val dest_Fact : thm -> string * thm
  val dest_AndFact_c : cterm -> cterm * cterm
  val elim_AndFact : thm -> thm * thm
  val elim_AndFacts : thm -> thm list

  (* `open_specthm (ctx,specthm)` puts auxiliary facts into the context by the name `\<nu>aux`
  *     and returns the focus proposition of the specification theorem.  *)
  val open_specthm  : thm -> Proof.context -> thm * Proof.context
  val open_specthm' : Position.T -> thm -> Proof.context -> thm * Proof.context
  (* get the auxiliary facts `\<nu>aux` which is usually stored by `open_specthm` *)
  val aux_facts : Proof.context -> thm list
  (* reassemble the specification theorem by the given focus proposition and the stored
  *     auxiliary facts `\<nu>aux` *)
  val close_specthm : thm -> Proof.context -> thm * Proof.context

  val start_construction_thm : thm

  val param_set_free_var_name : Proof.context -> string -> thm -> thm
end
structure NuBasics = struct
open Thm Term HOLogic NuHelp

fun perhaps f x = (f x) handle TERM _ => x | THM _ => x
val void_ty = Type("NuPrim.void", [])
fun proc_ctx_ty (a,b) = Type("NuPrim.proc_ctx", [a,b])
fun mk_stateT ty = Type("NuPrim.state", [ty])

val start_construction_thm = @{thm NuPrim.start_construction}

fun catch msg f tm = (f tm) handle TERM _ => raise TERM (msg, [tm])
fun catch_th i msg f th = (f th) handle THM _ => raise THM (msg, i, [th])
                                    | TERM _ => raise TERM (msg, [prop_of th])

fun dest_param (Const ("NuPrim.ParamTag", _) $ x) = x
  | dest_param tm = raise TERM ("dest_param", [tm])
val unit_const_name = "Product_Type.Unity"
val name_tag_ty = Type ("NuPrim.name_tag_ty", [])
val name_tag_const_name = "NuPrim.name_tag.NAME_TAG"
val unit_ty = Type ("Product_Type.unit", [])
val unit_const = Const("Product_Type.Unity", unit_ty)
val name_tag_const = Const (name_tag_const_name, (unit_ty --> unit_ty) --> name_tag_ty)
val dest_name_tag_raw   = dest_monop name_tag_const_name
val dest_name_tag_raw_c = dest_monop_c name_tag_const_name
fun dest_Abs (Abs x) =  x
  | dest_Abs t = raise TERM("dest_Abs", [t]);
fun dest_name_tag tm =
  tm |> Type.strip_constraints |> dest_name_tag_raw |> dest_Abs |> #1
    handle TERM _ => raise TERM ("dest_name_tag", [tm])
fun mk_name_tag name = name_tag_const $ Abs (name, unit_ty, unit_const)

val named_name = "NuPrim.Named"
fun dest_named tm =
  case try (dest_binop named_name) tm of
     SOME (v,tm) => (SOME (dest_name_tag v), tm)
   | NONE => (NONE, tm)
val nuTy_name = "NuPrim.NuTyp"
val dest_nuTy = dest_binop nuTy_name
fun dest_register (Const ("NuPrim.register.Register",_) $ name $ x) = (dest_name_tag name, x)
  | dest_register tm = raise TERM ("bad register",[tm])
fun dest_registerTy (Const ("NuPrim.RegisterTy",_) $ name $ x) = (dest_name_tag name, x)
  | dest_registerTy tm = raise TERM ("bad registerTy",[tm])
val Void_name = "NuPrim.Void"

fun dest_andTy (Const ("NuPrim.AndTy", _) $ t1 $ t2) = (t1, t2)
  | dest_andTy t = raise TERM ("bad AndTy", [t]);
fun dest_andTys tm =
  (case try dest_andTy tm of
        SOME (a,b) => BiTree.Node ((), dest_andTys a, dest_andTys b)
      | NONE => BiTree.Leaf ((),tm))
fun dest_registerTys regs = if same_const Void_name regs then NONE
  else SOME (BiTree.map_leaf (dest_registerTy #> #1) (dest_andTys regs))

val dest_SpecTop   = dest_binop "NuPrim.SpecTop"
val dest_SpecTop_c = dest_binop_c "NuPrim.SpecTop"
val dest_CurrentConstruction   = dest_binop "NuPrim.CurrentConstruction"
val dest_CurrentConstruction_c = dest_binop_c "NuPrim.CurrentConstruction"
val dest_PendingConstruction   = dest_triop "NuPrim.PendingConstruction"
val dest_PendingConstruction_c = dest_triop_c "NuPrim.PendingConstruction"
fun block_var_of_Constuction c   = (dest_CurrentConstruction c |> #1)
  handle TERM _ => ((dest_PendingConstruction c |> #2)
  handle TERM _ => raise TERM ("neithr CurrentConstruction nor PendingConstruction", [c]))
fun block_var_of_Constuction_c c = (dest_CurrentConstruction_c c |> #1)
  handle TERM _ => ((dest_PendingConstruction_c c |> #2)
  handle TERM _ => raise TERM ("neithr CurrentConstruction nor PendingConstruction", [term_of c]))
val dest_Proc_CtxTy   = dest_binop "NuPrim.Proc_CtxTy"
val dest_Proc_CtxTy_c = dest_binop_c "NuPrim.Proc_CtxTy"
val registers_of_specthm = catch_th 0 "registers_of_specthm: Not a CurrentConstruction"
  (Thm.cprop_of #> dest_SpecTop_c #> #1 #> dest_Trueprop_c
    #> dest_CurrentConstruction_c #> #2 #> dest_Proc_CtxTy_c #> #2)

val state_of_specthm = Thm.prop_of #> dest_SpecTop #> #1
val premise_of_specthm = state_of_specthm #> Logic.dest_implies #> #1
val current_block_var =
  state_of_specthm #> Logic.strip_assums_concl #> dest_Trueprop #> block_var_of_Constuction
val dest_codeblock   = perhaps dest_Trueprop #> dest_quadop "NuPrim.CodeBlock"
val codeblock_name   = dest_codeblock #> #1 #> dest_Free #> #1
val dest_codeblock_c = perhaps dest_Trueprop_c #> dest_quadop_c "NuPrim.CodeBlock"
val codeblocks_of   = hyps_of  #> filter (can dest_codeblock  )
val codeblocks_of_c = chyps_of #> filter (can dest_codeblock_c)
fun current_codeblock specthm =
  let
    val blk_var = current_block_var specthm
  in
    chyps_of specthm
  |> find_first (fn hy => (term_of hy |> try (dest_Trueprop #> dest_codeblock #> #1)) = SOME blk_var)
  |> Option.valOf
  end
fun disch_current_codeblock specthm = implies_intr (current_codeblock specthm) specthm

fun th1 MP th2 = Drule.comp_no_flatten (th1, 0) 1 th2
fun rule MP_BY args = fold (fn arg => fn rule => arg MP rule) args rule

val vP = (("P",0),propT) and vL = (("L",0),propT) and vQ = (("Q",0),propT)
fun elim_SPEC th = 
  let
    val (P,L) = dest_SpecTop_c (cprop_of th)
    val inst = Thm.instantiate ([],[(vP,P),(vL,L)])
  in
   (Thm.implies_elim (inst @{thm SpecTop_focus}) th,
    Thm.implies_elim (inst @{thm SpecTop_facts}) th)
  end
fun intro_SPEC (focus,facts) = 
  Thm.implies_elim
    (Thm.implies_elim
      (Thm.instantiate ([],[(vP, cprop_of focus), (vL, cprop_of facts)]) @{thm NuPrim.SpecTop_I})
    focus)
  facts


val dest_fact   = dest_binop   "NuPrim.Fact" #> apfst dest_name_tag
val dest_fact_c = dest_binop_c "NuPrim.Fact" #> apfst (term_of #> dest_name_tag)
val vP = (("P",0), HOLogic.boolT)
fun dest_Fact th =
  let
    val (_,P) = th |> cprop_of |> dest_fact_c
  in
    th |> Thm.implies_elim (Thm.instantiate ([],[(vP, P)]) @{thm NuPrim.Fact_D})
  end
val dest_AndFact_c = dest_binop_c "NuPrim.AndFact"
fun elim_AndFact th =
  let
    val (P, Q) = dest_AndFact_c (Thm.cprop_of th)
      handle TERM (msg, _) => raise THM (msg, 0, [th]);
    val inst = Thm.instantiate ([], [(vP, P), (vQ, Q)]);
  in
   (Thm.implies_elim (inst @{thm AndFact_D1}) th,
    Thm.implies_elim (inst @{thm AndFact_D1}) th)
  end
fun elim_AndFacts_impl ret [] = ret
  | elim_AndFacts_impl ret (th::r) = 
      (case try elim_AndFact th of
        NONE => 
          if same_const "NuPrim.NoFact" (prop_of th)
          then elim_AndFacts_impl ret r
          else elim_AndFacts_impl ((dest_Fact th)::ret) r
      | SOME (th1, th2) => elim_AndFacts_impl ret (th1::th2::r))
val elim_AndFacts = elim_AndFacts_impl [] o single

val thm_PropBlock_I = @{thm NuPrim.PropBlock_I}
fun mk_PropBlock n th = Drule.comp_no_flatten (th, n) 1 thm_PropBlock_I

val thm_ParamTag_E = @{thm NuPrim.ParamTag_E}
fun param_set_free_var_name ctx name thm =
  let
    val param_var as (_, param_ty) = prems_of thm |> hd |> dest_param |> dest_Var
  in
    instantiate ([], [(param_var, cterm_of ctx (Free (name, param_ty)))]) thm
      |> (fn x => thm_ParamTag_E RS x)
  end

val aux_name = "that" and aux_name_raw = "\<nu>aux'raw"
fun open_specthm' pos th ctx =
  (case elim_SPEC th of (focus,aux) =>
    ctx |> Proof_Context.put_thms false (aux_name_raw, SOME [aux])
      |> Proof_Context.add_thms_lazy "" (Binding.make(aux_name, pos),
          Lazy.lazy (fn _ => elim_AndFacts aux @ Assumption.all_prems_of ctx))
      |> pair focus)
val open_specthm = open_specthm' Position.none
fun aux_facts ctx = Proof_Context.get_thms ctx aux_name
fun aux_facts_raw ctx = Proof_Context.get_thm ctx aux_name_raw
fun close_specthm focus ctx =
  ctx |> Proof_Context.put_thms false (aux_name_raw, NONE)
    |> Proof_Context.put_thms false (aux_name, NONE)
    |> pair (intro_SPEC (focus, aux_facts_raw ctx))


val dest_procedure   = dest_triop   "NuPrim.Procedure" o perhaps dest_Trueprop
val dest_procedure_c = dest_triop_c "NuPrim.Procedure" o perhaps dest_Trueprop_c
end
