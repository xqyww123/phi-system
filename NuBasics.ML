(*  Title:      NuBasics.ML
    Author:     Qiyuan Xu

Basic supports for the nu-system.

*)
infix 0 MP MP_BY

signature NU_BASICS = sig
  exception NDBG of thm
  val repeate : ('a -> 'a) -> 'a -> 'a
  val ntimes : int -> ('a -> 'a) -> 'a -> 'a

  val void_ty : typ
  val mk_stateT : typ -> typ
  val dest_tynuset_c : ctyp -> ctyp
  val dest_typroc_c : ctyp -> ctyp * ctyp

  val dest_param : term -> term
  val param_type : thm -> typ
  val dest_RepSet : term -> term * term
  val dest_nuTy : term -> term * term
  val mk_nuTy : term * term -> term
  val dest_named_opt : term -> string option * term (* Named name, x -> (name,x) *)
  val name_tag_ty : typ
  val name_tag_cty : ctyp
  val dest_name_tag : term -> string
  val mk_name_tag : string -> term
  val mk_name_tag_c : string -> cterm
  val mk_repset : term -> term
  val Void_name : string
  (* val dest_andTy : term -> term * term *)
  val dest_SpecTop   : term -> term * term
  val dest_SpecTop_c : cterm -> cterm * cterm
  val dest_CurrentConstruction : term -> term * term
  val dest_CurrentConstruction_c : cterm -> cterm * cterm
  val dest_PendingConstruction : term -> term * term * term
  val dest_PendingConstruction_c : cterm -> cterm * cterm * cterm
  val dest_current_nu   : thm -> term
  val stack_of_meta   : thm -> term list
  val block_var_of_Constuction : term  -> term
  val block_var_of_Constuction_c : cterm  -> cterm
  val current_block_var   : thm -> term
  val current_block_var_c : thm -> cterm
  val current_block_depth : thm -> int
  val dest_codeblock   : term -> term * term * term * term
  val dest_codeblock_c : cterm -> cterm * cterm * cterm * cterm
  val codeblocks_of   : thm -> term list
  val codeblocks_of_c : thm -> cterm list
  val codeblock_name   : term -> term * term * term * term
  val current_codeblock : thm -> cterm
  val export_codeblock : cterm * cterm -> thm -> thm
  val export_codeblocks : cterm list -> thm -> thm

  val dest_procedure   : term -> term * term * term
  val dest_procedure_c : cterm -> cterm * cterm * cterm
  val dest_premise_tag  : term -> term
  val dest_premise_tag_c: cterm -> cterm
  val dest_simplify_tag   : term -> term * term
  val dest_simplify_tag_c : term -> cterm * cterm

  val elim_SPEC : thm -> thm * thm
  val intro_SPEC : thm * thm -> thm
  val map_major : (thm -> thm) -> thm -> thm
  val mk_PropBlock : int -> thm -> thm

  val dest_fact : term -> string * term
  val dest_fact_c : cterm -> string * cterm
  val name_of_Fact : thm -> string
  val elim_Fact : thm -> string * thm
  val intro_Fact : string * thm -> thm
  val dest_AndFact : term -> term * term
  val dest_AndFact_c : cterm -> cterm * cterm
  val dest_AndFacts : term -> term list
  val elim_AndFact : thm -> thm * thm
  val intro_AndFact : thm * thm -> thm
  val elim_AndFacts : thm -> thm list
  val intro_AndFacts : thm list -> thm
  val dest_FactCollection   : term -> term * term * term
  val dest_FactCollection_c : cterm -> cterm * cterm * cterm
  val elim_FactCollection : thm -> thm * thm * thm
  val intro_FactCollection : thm * thm * thm -> thm
  val user_facts_in_collection : thm -> (string * thm) list
  (* val intro_interal_fact : thm (* thm to be added *) -> thm (* fact collection *) -> (int * thm)
  val intro_interal_fact_spec : thm (* thm to be added *) -> thm (* specthm *)
  -> (int * thm) *)
  val clean_user_facts : thm -> thm

  (* Transform every HOL part of the facts theorem, including star fact, every user fact, and every
  * internal fact. *)
  val holrule : (thm -> thm) -> thm -> thm

  val dest_Cast   : term -> term * term * term
  val dest_Cast_c : cterm -> cterm * cterm * cterm
  val expand_proc : thm -> thm
  val apply_proc_naive : thm (*proc*) -> thm (*meta or major*) -> thm

  val intro_param : cterm -> thm
  val intro_param_name : string -> thm

  val param_set_free_var_name : Proof.context -> string -> thm -> thm
  (* val auto_fusion_arity : term -> int *)

  val parse_arg_list : term -> term
end
structure NuBasics = struct
open Thm Term HOLogic NuHelp
exception NDBG of thm

fun repeate f x = repeate f (f x) handle TERM _ => x | THM _ => x
fun ntimes n f x = if n <= 0 then x else ntimes (n-1) f (f x)
fun perhaps f x = (f x) handle TERM _ => x | THM _ => x
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

fun dest_param (Const (@{const_name "ParamTag"}, _) $ x) = x
  | dest_param tm = raise TERM ("dest_param", [tm])
val dest_param_c = dest_monop_c @{const_name "ParamTag"}
fun param_type_c th = cprem_of th 1 |> dest_param_c |> ctyp_of_cterm
val param_type = param_type_c #> typ_of
val unit_const_name = @{const_name "Product_Type.Unity"}
val name_tag_ty = Type (@{type_name "name_tag"}, [])
val name_tag_cty = @{ctyp "name_tag"}
val name_tag_const_name = @{const_name "NAME_TAG"}
val unit_ty = Type (@{type_name "Product_Type.unit"}, [])
val unit_const = Const("Product_Type.Unity", unit_ty)
val name_tag_const = Const (name_tag_const_name, (unit_ty --> unit_ty) --> name_tag_ty)
val dest_name_tag_raw   = dest_monop name_tag_const_name
val dest_name_tag_raw_c = dest_monop_c name_tag_const_name
fun dest_Abs (Abs x) =  x
  | dest_Abs t = raise TERM("dest_Abs", [t]);
fun dest_name_tag tm =
  tm |> Type.strip_constraints |> dest_name_tag_raw |> dest_Abs |> #1
    handle TERM _ => raise TERM ("dest_name_tag", [tm])
val name_tag_c = @{cterm "NAME name"}
fun mk_name_tag name = name_tag_const $ Abs (name, unit_ty, unit_const)
fun mk_name_tag_c name = renamed_term (mk_name_tag name) name_tag_c

val named_name = @{const_name "Named"}
val dest_named = dest_binop named_name #> apfst dest_name_tag
fun dest_named_opt tm =
  case try (dest_binop named_name) tm of
     SOME (v,tm) => (SOME (dest_name_tag v), tm)
   | NONE => (NONE, tm)
fun mk_repset (tm as (Const (@{const_name "RepSet"}, _) $ _)) = tm
  | mk_repset tm = mk_monop @{const_name "RepSet"} tm
val nuTy_name = @{const_name "typing"}
val dest_nuTy = dest_binop nuTy_name
val dest_RepSet = dest_monop @{const_name "RepSet"} #> dest_nuTy
val mk_nuTy = mk_binop nuTy_name
(* fun dest_andTy (Const (@{const_name "AndTy"}, _) $ t1 $ t2) = (t1, t2)
  | dest_andTy t = raise TERM ("bad AndTy", [t]); *)

val dest_SpecTop   = dest_binop @{const_name "SpecTop"}
val dest_SpecTop_c = dest_binop_c @{const_name "SpecTop"}
val dest_CurrentConstruction   = dest_binop @{const_name "CurrentConstruction"}
val dest_CurrentConstruction_c = dest_binop_c @{const_name "CurrentConstruction"}
val dest_PendingConstruction   = dest_triop @{const_name "PendingConstruction"}
val dest_PendingConstruction_c = dest_triop_c @{const_name "PendingConstruction"}
fun block_var_of_Constuction c   = (dest_CurrentConstruction c |> #1)
  handle TERM _ => ((dest_PendingConstruction c |> #2)
  handle TERM _ => raise TERM ("neithr CurrentConstruction nor PendingConstruction", [c]))
fun block_var_of_Constuction_c c = (dest_CurrentConstruction_c c |> #1)
  handle TERM _ => ((dest_PendingConstruction_c c |> #2)
  handle TERM _ => raise TERM ("neithr CurrentConstruction nor PendingConstruction", [term_of c]))
val dest_current_nu = Thm.prop_of #> perhaps (dest_SpecTop #> #1) #> perhaps dest_Trueprop
    #> dest_CurrentConstruction #> #2
fun strip_stack ret (Const (@{const_name "Pair"}, _) $ a $ b,
                     Const (@{const_name "Stack_Delimiter"}, _) $ A $ B)
      = strip_stack ((a,A)::ret) (b,B)
  | strip_stack ret (a,A) = (a,A)::ret
fun dest_topctx (Const (@{const_name "Pair"}, _) $ a $ b,
                 Const (@{const_name "NuTopCtx"}, _) $ A $ B)
      = ((a,A),(b,B))
val stack_of_meta = catch_th 0 "stack_of_meta: Not a CurrentConstruction"
  (dest_current_nu #> dest_RepSet
    #> apsnd (repeate (dest_binop @{const_name "NuAddition"} #> #1))
    #> dest_topctx #> #2
    #> strip_stack [])

val current_block_var_c =
  Thm.cprop_of
    #> perhaps (dest_SpecTop_c #> #1)
    #> perhaps strip_implies_c
    #> perhaps dest_Trueprop_c
    #> block_var_of_Constuction_c
val current_block_var =
  Thm.prop_of
    #> perhaps (dest_SpecTop #> #1)
    #> perhaps Logic.strip_assums_concl
    #> perhaps dest_Trueprop
    #> block_var_of_Constuction
val dest_codeblock   = perhaps dest_Trueprop #> dest_quadop @{const_name "NuPrime.CodeBlock"}
val codeblock_name   = dest_codeblock #> #1 #> dest_Free #> #1
val dest_codeblock_c = perhaps dest_Trueprop_c #> dest_quadop_c @{const_name "NuPrime.CodeBlock"}
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
val thm_codeblock_export = @{thm NuPrime.codeblock_export}
fun aconv_c (ctm1,ctm2) = aconv (term_of ctm1, term_of ctm2)
val prop_term = @{cterm Pure.prop}
fun export_codeblock (codeblock,destined_codeblock) th =
  if aconv_c (codeblock,destined_codeblock) then th
  else let
    val (s,_,_,_) = dest_codeblock_c destined_codeblock
    val goal = cprop_of (disch_codeblock destined_codeblock th)
          |> Thm.apply prop_term |> Goal.init
    val endth = disch_codeblock codeblock th |> Goal.protect 0
    fun loop th = (endth RS th |> Goal.conclude)
      handle THM _ => loop (thm_codeblock_export RS th)
  in
    loop goal |> Goal.conclude |> undisch_codeblock s
  end
  handle THM e => (@{print} e; raise THM ("export_codeblock", 1,
    [th, Thm.assume codeblock, Thm.assume destined_codeblock]))
fun export_codeblocks destined_codeblocks th =
  let
    val codeblock_name = term_of #> dest_codeblock #> #1 #> term_name
    val destined = fold (fn cb => Symtab.update_new (codeblock_name cb, cb))
          destined_codeblocks Symtab.empty
    val exports = chyps_of th |> List.mapPartial (fn cb =>
            cb |> try codeblock_name
               |> Option.mapPartial (Symtab.lookup destined)
               |> Option.map (pair cb))
  in
    fold export_codeblock exports th
  end


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
      (Thm.instantiate ([],[(vP, cprop_of focus), (vL, cprop_of facts)]) @{thm NuPrime.SpecTop_I})
    focus)
  facts
fun map_major f th =
  if can (dest_SpecTop o prop_of) th then elim_SPEC th |> apfst f |> intro_SPEC
  else f th


val dest_fact   = dest_binop   @{const_name "Fact"} #> apfst dest_name_tag
val dest_fact_c = dest_binop_c @{const_name "Fact"} #> apfst (term_of #> dest_name_tag)
val vP = (("P",0), HOLogic.boolT) and v_label = (("label",0),name_tag_ty)
val Fact_D = @{thm NuPrime.Fact_D} and Fact_I = @{thm NuPrime.Fact_I}
fun name_of_Fact th = th |> cprop_of |> dest_fact_c |> #1
fun elim_Fact th =
  let
    val (name,P) = th |> cprop_of |> dest_fact_c
  in
    th |> Thm.implies_elim (Thm.instantiate ([],[(vP, P)]) Fact_D)
       |> pair name
  end
fun intro_Fact (name,th) =
  Thm.implies_elim
    (Thm.instantiate ([],[(v_label, mk_name_tag_c name), (vP, cprop_of th)]) Fact_I) th
val dest_AndFact   = dest_binop   @{const_name "AndFact"}
val dest_AndFact_c = dest_binop_c @{const_name "AndFact"}
fun dest_AndFacts_impl ret tm =
  if same_const @{const_name "NoFact"} tm then rev ret
  else (case dest_AndFact tm of (a,b) => dest_AndFacts_impl (a::ret) b)
val dest_AndFacts = dest_AndFacts_impl []
val vP = (("P",0),propT) and vQ = (("Q",0),propT) and vS = (("S",0),propT)
val AndFact_D1 = @{thm AndFact_D1}
and AndFact_D2 = @{thm AndFact_D2}
and AndFact_I = @{thm AndFact_I}
val NoFact = @{thm NuPrime.NoFact}
fun elim_AndFact th =
  let
    val (P, Q) = dest_AndFact_c (Thm.cprop_of th)
      handle TERM (msg, _) => raise THM ((msg, 0, [th]));
    val inst = Thm.instantiate ([], [(vP, P), (vQ, Q)]);
  in
   (Thm.implies_elim (inst AndFact_D1) th,
    Thm.implies_elim (inst AndFact_D2) th)
  end
fun intro_AndFact (th1,th2) =
  Drule.implies_elim_list
    (Thm.instantiate ([],[(vP, cprop_of th1), (vQ, cprop_of th2)]) AndFact_I)
    [th1,th2]
fun elim_AndFacts_impl ret [] = ret
  | elim_AndFacts_impl ret (th::r) = 
      (case try elim_AndFact th of
        NONE => 
          if same_const @{const_name "NoFact"} (prop_of th)
          then elim_AndFacts_impl ret r
          else elim_AndFacts_impl (th::ret) r
      | SOME (th1, th2) => elim_AndFacts_impl ret (th1::th2::r))
val elim_AndFacts = rev o elim_AndFacts_impl [] o single
fun intro_AndFacts l = fold_rev (fn th1 => fn th2 => intro_AndFact (th1,th2)) l NoFact
val dest_FactCollection   = dest_triop   @{const_name "FactCollection"}
val dest_FactCollection_c = dest_triop_c @{const_name "FactCollection"}
val th_FactCollection_D1 = @{thm NuPrime.FactCollection_D1}
and th_FactCollection_D2 = @{thm NuPrime.FactCollection_D2}
and th_FactCollection_D3 = @{thm NuPrime.FactCollection_D3}
and th_FactCollection_I  = @{thm NuPrime.FactCollection_I}
fun elim_FactCollection th =
  let
    val (P,Q,S) = cprop_of th |> dest_FactCollection_c
  in
    (Thm.implies_elim (Thm.instantiate ([],[(vP,P),(vQ,Q),(vS,S)]) th_FactCollection_D1) th,
     Thm.implies_elim (Thm.instantiate ([],[(vP,P),(vQ,Q),(vS,S)]) th_FactCollection_D2) th,
     Thm.implies_elim (Thm.instantiate ([],[(vP,P),(vQ,Q),(vS,S)]) th_FactCollection_D3) th)
  end
fun intro_FactCollection (th1,th2,th3) =
  Drule.implies_elim_list
    (Thm.instantiate ([],[(vP, cprop_of th1), (vQ, cprop_of th2), (vS, cprop_of th3)])
      th_FactCollection_I) [th1,th2,th3]
fun user_facts_in_collection th =
  let
    val (P,Q,S) = elim_FactCollection th
    val ths = elim_AndFacts Q |> map elim_Fact
  in
    if same_const @{const_name "NoFact"} (prop_of P) then ths else ("\<glowing_star>",P)::ths
  end
val vA = (("A",0),propT) and vP = (("P",0),propT) and vQ = (("Q",0),propT) and vL = (("L",0),propT)
(* fun intro_interal_fact A th =
  let
    val (Q,L,S) = cprop_of th |> dest_FactCollection_c
    val intro_thm =
      Thm.instantiate ([],[(vA, cprop_of A), (vQ,Q), (vL,L), (vS,S)]) intro_internal_fact_thm
    val id = length (dest_AndFacts (term_of S))
    val th = Thm.implies_elim (Thm.implies_elim intro_thm A) th
  in (id,th) end
fun intro_interal_fact_spec A th =
  let
    val (focus,facts) = elim_SPEC th
    val (id,facts') = intro_interal_fact A facts
  in
    (id, intro_SPEC (focus, facts'))
  end *)
val clean_user_facts_thm = @{thm NuPrime.clean_user_facts}
fun clean_user_facts th = th RS clean_user_facts_thm

fun apply3 f (a,b,c) = (f a, f b, f c)
fun holrule f th =
  case prop_of th
    of (Const (@{const_name "AndFact"},_) $ _ $ _) =>
         elim_AndFact th |> apply2 (holrule f) |> intro_AndFact
     | (Const (@{const_name "SpecTop"},_) $ _ $ _) =>
         elim_SPEC th |> apply2 (holrule f) |> intro_SPEC
     | (Const (@{const_name "FactCollection"},_) $ _ $ _ $ _) =>
         elim_FactCollection th |> apply3 (holrule f) |> intro_FactCollection
     | (Const (@{const_name "Fact"},_) $ _ $ _) =>
         elim_Fact th |> apsnd (holrule f) |> intro_Fact
     | (Const (@{const_name "HOL.Trueprop"}, _) $ _) => f th
     | (Const (@{const_name "Pure.imp"}, _) $ _ $ _) => f th
     | (Const (@{const_name "NoFact"}, _)) => NoFact
     | tm => raise TERM ("holrule", [tm])


val thm_ParamTag = @{thm NuPrime.ParamTag}
fun param_set_free_var_name ctx name thm =
  let
    val param_var as (_, param_ty) = prems_of thm |> hd |> dest_param |> dest_Var
  in
    instantiate ([], [(param_var, cterm_of ctx (Free (name, param_ty)))]) thm
      |> (fn x => thm_ParamTag RS x)
  end

val dest_procedure   = perhaps dest_Trueprop
  #> strip_binder @{const_name All} #> #2
  #> strip_binop_r @{const_name HOL.implies} #> last
  #> dest_triop @{const_name "Procedure"}
val dest_procedure_c = perhaps dest_Trueprop_c
  #> strip_binder_c @{const_name All} #> #2
  #> strip_binop_r_c @{const_name HOL.implies} #> last
  #> dest_triop_c @{const_name "Procedure"}
val dest_premise_tag  = dest_monop   @{const_name "NuPrime.Premise"} o perhaps dest_Trueprop
val dest_premise_tag_c= dest_monop_c @{const_name "NuPrime.Premise"} o perhaps dest_Trueprop_c
val dest_simplify_tag   = dest_binop   @{const_name "NuPrime.Simplify"}
val dest_simplify_tag_c = dest_binop_c @{const_name "NuPrime.Simplify"}

val vx = ("x",0) and va = ("'a",0)
fun intro_param tm =
  Thm.instantiate ([((("'a",0), ["HOL.type"]), ctyp_of_cterm tm)],
                   [((("x",0), typ_of (ctyp_of_cterm tm)), tm)]) @{thm ParamTag}
val intro_param_name = intro_param o mk_name_tag_c

val dest_Cast   = dest_triop   @{const_name "Cast"}
val dest_Cast_c = dest_triop_c @{const_name "Cast"}

val expand_proc = 
  repeate (fn th => th RS @{thm spec}) #> 
  repeate (fn th => th RS @{thm mp})

val thm_apply_proc = @{thm apply_proc}
fun apply_proc_naive proc =
  map_major (fn major => expand_proc proc RS (major RS thm_apply_proc))

(* val auto_fusion_arity =
  Logic.strip_assums_concl #> perhaps dest_Trueprop #> perhaps (dest_procedure #> #2)
  #> perhaps (dest_binop "NuPrime.Stack_Delimiter" #> #2)
  #> perhaps dest_RepSet #> perhaps (dest_nuTy #> #2)
  #> repeate (dest_binop "NuBasicAbstractors.NuRefine" #> #1)
  #> repeate (dest_binop "NuBasicAbstractors.SchemaCondition" #> #1)
  #> repeate (dest_binop "NuBasicAbstractors.Schema" #> #1)
  #> strip_binop_r "NuLLReps.AutoFusion" #> length *)

local
fun is_free_var' tm = is_Free tm orelse is_Var tm
fun is_free_var tm = is_free_var' (Type.strip_constraints tm)
in

fun tr_stack (Const (@{const_name Pair}, ty1) $ a $ b, Const (@{const_name Stack_Delimiter},ty2) $ A $ B)
    = (case tr_stack (b, B) of (b', B') =>
        (Const (@{const_name Pair}, ty1) $ a $ b', Const (@{const_name Stack_Delimiter},ty2) $ A $ B'))
  | tr_stack (ab as (a, A)) = if is_free_var a andalso is_free_var A then ab else
        (Const (@{const_name Pair}, dummyT) $ a $ Free ("\<rr>", dummyT),
          Const (@{const_name Stack_Delimiter},dummyT) $ A $ Free ("\<RR>", dummyT))
fun tr_heap (Const (@{const_name Pair}, ty1) $ a $ b, Const (@{const_name Heap_Delimiter},ty2) $ A $ B)
    = (case tr_heap (b, B) of (b', B') =>
        (Const (@{const_name Pair}, ty1) $ a $ b', Const (@{const_name Heap_Delimiter},ty2) $ A $ B'))
  | tr_heap (ab as (a, A)) = if is_free_var a andalso is_free_var A then ab else
        (Const (@{const_name Pair}, dummyT) $ a $ Free ("\<hh>", dummyT),
          Const (@{const_name Heap_Delimiter},dummyT) $ A $ Free ("\<HH>", dummyT))

fun tr_topctx (Const (@{const_name Pair}, ty1) $ a $ b, Const (@{const_name NuTopCtx},ty2) $ A $ B)
    = let val (a',A') = tr_heap (a, A); val (b', B') = tr_stack (b,B)
       in (Const (@{const_name Pair}, ty1) $ a' $ b', Const (@{const_name NuTopCtx},ty2) $ A' $ B') end
  | tr_topctx (a, A) =
       let val (a',A') = tr_stack (a, A)
       in (Const (@{const_name Pair}, dummyT) $ Free ("\<hh>", dummyT) $ a',
             Const (@{const_name NuTopCtx},dummyT) $ Free ("\<HH>", dummyT) $ A') end

fun tr_final tr tm = mk_nuTy (tr (dest_nuTy tm))

val parse_arg_list = tr_final tr_topctx

end
end
