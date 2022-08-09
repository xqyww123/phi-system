(*  Title:      NuBasics.ML

Basic supports for the nu-system.

*)
infix 0 MP MP_BY

signature NU_BASICS = sig
  exception NDBG of thm

  val under_programming_environ : Proof.context -> bool
  val the_construction : Proof.context -> thm
  val the_programming_sequent' : Proof.context -> thm
  val the_nu_fact : Proof.state -> thm
  val set_nu_fact : thm -> Proof.state -> Proof.state
  val set_programming_sequent' : thm -> Proof.context -> Proof.context


  val dest_param : term -> term
  val param_type : thm -> typ
  val dest_labelled_opt : term -> string option * term (* Labelled name, x -> (name,x) *)
  val label_ty : typ
  val label_cty : ctyp
  val dest_label : term -> string
  val mk_label : string -> term
  val mk_label_c : string -> cterm
  val mk_labelled : string -> term -> term
  val mk_name_hint : string -> term -> term
  val mk_label_thm : string -> thm

  val dest_Cast   : term -> term * term * term
  val dest_Cast_c : cterm -> cterm * cterm * cterm

  val intro_param : cterm -> thm
  val intro_param_name : string -> thm

  val param_set_free_var_name : Proof.context -> string -> thm -> thm
  (* val auto_fusion_arity : term -> int *)
end
structure NuBasics : NU_BASICS = struct
open Thm Term HOLogic NuHelp
exception NDBG of thm

structure Programming_Sequent = Proof_Data (
  type T = (thm (*sequent*)
          * thm (*the latest construction*)
          * thm list lazy (*implication*)
          ) option;
  val init = (K NONE)
)

fun err_bad_env () = warning("Not in the \<phi> programming environment")

fun the_construction ctxt =
  case Programming_Sequent.get ctxt of SOME (_,thm, _) => thm
                                     | _ => (err_bad_env (); Drule.dummy_thm)

val under_programming_environ = is_some o Programming_Sequent.get

fun the_programming_sequent' ctxt =
  case Programming_Sequent.get ctxt of SOME (thm, _, _) => thm
                                     | _ => (err_bad_env (); Drule.dummy_thm)

val the_nu_fact = the_programming_sequent' o Proof.context_of

fun the_implication' ctxt =
  case Programming_Sequent.get ctxt of SOME (_, _, imp) => Lazy.force imp
                                     | _ => (err_bad_env (); [])

fun reason_programming_implication ctxt sequent =
  let
    val CurrentConstruction_mk_elim_rule =
            Proof_Context.get_thm ctxt "local.CurrentConstruction_mk_elim_rule"
    val stat = (sequent RS CurrentConstruction_mk_elim_rule)
                  |> pair ctxt |> SOME
               handle THM _ => NONE
  in case Option.mapPartial Nu_Reasoner.reason stat
       of SOME (_, result) => [result]
        | _ => []
  end

fun set_programming_sequent' sequent ctxt =
  let
    val is_construction =
          case Thm.prop_of sequent
            of \<^const>\<open>Trueprop\<close> $ P => NuHelp.has_head \<^const_name>\<open>\<phi>empty.CurrentConstruction\<close> P
             | _ => false
    fun put data = Programming_Sequent.put (SOME data) ctxt
  in
    if is_construction
    then put (sequent, sequent, Lazy.lazy (fn () => reason_programming_implication ctxt sequent))
    else
      case Programming_Sequent.get ctxt
        of SOME (_, construction, implication) => put (sequent, construction, implication)
         | NONE => put (sequent, sequent, Lazy.value [])
  end
  

fun set_nu_fact sequent stat = stat
  |> Proof.set_facts [sequent]
  |> Proof.map_context (set_programming_sequent' sequent);

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>this\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => (err_bad_env (); [])
               | Context.Proof ctxt => [the_programming_sequent' ctxt]))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>construction\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => (err_bad_env (); [])
               | Context.Proof ctxt => [the_construction ctxt]))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>implication\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt => the_implication' ctxt))

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>\<close>,
          (fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt =>
                   ( Proof_Context.get_thms ctxt "\<phi>implication"
                   @ Proof_Context.get_thms ctxt \<^named_theorems>\<open>\<phi>lemmata\<close>
                   @ Proof_Context.get_thms ctxt \<^named_theorems>\<open>useful\<close>)
          )))


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
  Thm.instantiate (TVars.empty, Vars.make [((("x",0),\<^typ>\<open>label\<close>), mk_label_c name)]) @{thm LabelTag}
fun mk_labelled name tm = Const(@{const_name Labelled}, dummyT) $ mk_label name $ tm
fun mk_name_hint name tm = Const(@{const_name NameHint}, dummyT) $ mk_label name $ tm

val labelled_name = @{const_name "Labelled"}
val dest_labelled = dest_binop labelled_name #> apfst dest_label
fun dest_labelled_opt tm =
  case try (dest_binop labelled_name) tm of
     SOME (v,tm) => (SOME (dest_label v), tm)
   | NONE => (NONE, tm)





val thm_ParamTag = @{thm ParamTag}
fun param_set_free_var_name ctx name thm =
  let
    val param_var as (_, param_ty) = prems_of thm |> hd |> dest_param |> dest_Var
  in
    instantiate (TVars.empty, Vars.make [(param_var, cterm_of ctx (Free (name, param_ty)))]) thm
      |> (fn x => thm_ParamTag RS x)
  end


val vx = ("x",0) and va = ("'a",0)
fun intro_param tm =
  Thm.instantiate (TVars.make [((("'a",0), ["HOL.type"]), ctyp_of_cterm tm)],
                   Vars.make  [((("x",0), typ_of (ctyp_of_cterm tm)), tm)]) @{thm ParamTag}
val intro_param_name = intro_param o mk_label_c

val dest_Cast   = dest_triop   @{const_name "Subty"}
val dest_Cast_c = dest_triop_c @{const_name "Subty"}



(* val auto_fusion_arity =
  Logic.strip_assums_concl #> perhaps (try dest_Trueprop) #> perhaps_try (dest_procedure #> #2)
  #> perhaps_try (dest_binop "NuPrime.Stack_Delimiter" #> #2)
  #> perhaps (try dest_RepSet) #> perhaps_try (dest_nuTy #> #2)
  #> repeat (dest_binop "NuBasicAbstractors.NuRefine" #> #1)
  #> repeat (dest_binop "NuBasicAbstractors.SchemaCondition" #> #1)
  #> repeat (dest_binop "NuBasicAbstractors.Schema" #> #1)
  #> strip_binop_r "NuLLReps.AutoFusion" #> length *)

(*default type remander*)
(* val default_ty_R = TFree ("'\<RR>", [@{class "stack"}]) *)
(*translate tail of a stack type to `ty_R`, if it ends with void*)







end
