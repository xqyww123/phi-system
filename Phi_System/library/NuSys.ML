(* The Signature *)
signature NU_SYS = sig
  (** Basic Operations **)
  val cast : cterm -> Proof.context * thm -> Proof.context * thm
  val cast_exception : cterm -> Proof.context * thm -> Proof.context * thm
  val move_lemmata : context_state -> context_state
  val apply_automatic_morphism : context_state -> context_state

  val accept_proc : context_state -> context_state

  val set_param : term -> context_state -> context_state
  val set_param_cmd : string -> context_state -> context_state
  val set_label : string -> context_state -> context_state

  val synthesis : cterm -> context_state -> context_state

  val setup_proof : (Proof.context -> (string * string) * (string * thm list) list -> unit)
        -> Proof_Context.mode -> bool -> string -> Method.text option
        -> (Proof.context * thm list list -> Proof.state -> Proof.state)
        -> (binding * typ option * mixfix) list (*fixes*)
        -> (Thm.binding * (term * term list) list) list (*premis*)
        -> (term * term list) list list (*no binding is allowed*)
        -> Proof.state -> thm list * Proof.state
  val obligation_proof :  (Proof.context -> (string * string) * (string * thm list) list -> unit)
        -> Proof_Context.mode -> bool -> string -> Method.text option
        -> (thm -> Proof.state -> Proof.state)
        -> (binding * typ option * mixfix) list
        -> (Thm.binding * (term * term list) list) list
        -> thm -> Proof.state -> thm list * Proof.state
end

(* The Structure *)
structure NuSys : NU_SYS = struct
open Thm NuBasics Term

(*fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg'' th = Seq.make (fn () => (@{print} th; raise NDBG th))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty))) *)

(** Morphism **)

structure Morphism = Proof_Data (
  type T = thm list
  val init = K []
);

val _ = Theory.setup (Global_Theory.add_thms_dynamic (\<^binding>\<open>\<phi>morphism\<close>,
          fn genric =>
              case genric
              of Context.Theory _ => []
               | Context.Proof ctxt => Morphism.get ctxt))

(** Basic Operations **)

val cast = Phi_Working_Mode.cast
val cast_exception = Phi_Working_Mode.cast_exception

fun apply_automatic_morphism' _ [] _ = raise Empty
  | apply_automatic_morphism' R (M::L) stat =
      case Thm.concl_of M
        of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Morphism\<close>, _) $ \<^const>\<open>MODE_AUTO\<close> $ _ $ _)
             => (rev R @ L, NuApply.apply [M] stat)
         | _ =>apply_automatic_morphism' (M::R) L stat

fun apply_automatic_morphism (ctxt,sequent) =
  case apply_automatic_morphism' [] (Morphism.get ctxt) (ctxt,sequent)
    of (R, stat') => apfst (Morphism.put R) stat'

fun simplify_morphisms _   [] = []
  | simplify_morphisms ctxt L =
      map (Raw_Simplifier.rewrite_rule ctxt @{thms FOCUS_TAG_def[folded atomize_eq]}) L

fun move_lemmata' (ctxt, sequent) =
  let
    fun filter_lemma th =
      case Thm.prop_of th
        of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>USELESS\<close> $ _) => NONE
         | \<^const>\<open>Trueprop\<close> $ \<^const>\<open>True\<close> => NONE
         | _ => SOME th
    fun is_morphism th =
      case Thm.concl_of th
        of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Morphism\<close>, _) $ _ $ _ $ _) => true
         | _ => false
    val all_lemmas = (sequent RS @{thm conjunct2})
                  |> HOLogic.conj_elims ctxt
                  |> map_filter filter_lemma
    val lemmas = all_lemmas |> filter (not o is_morphism)
    val morphisms = all_lemmas |> filter is_morphism |> simplify_morphisms ctxt
    val ctxt' =
      if null lemmas
      then ctxt
      else Context.proof_map (fold (fn th =>
              Named_Theorems.add_thm \<^named_theorems>\<open>\<phi>lemmata\<close> th
            #>Named_Theorems.add_thm \<^named_theorems>\<open>useful\<close> th
           ) lemmas) ctxt
    val ctxt'' =
      if null morphisms
      then ctxt'
      else Morphism.map (fn L => morphisms@L) ctxt'
  in
    (ctxt'', sequent RS @{thm conjunct1})
  end

fun move_lemmata (ctxt, sequent) =
  case Thm.prop_of sequent
    of \<^const>\<open>Trueprop\<close> $ (\<^const>\<open>conj\<close> $ _ $ _) => move_lemmata (move_lemmata' (ctxt, sequent))
     | _ => (ctxt, sequent)


fun export_codeblock _ param_cterms rule assm sequent =
     sequent |> Thm.implies_intr assm
             |> Drule.forall_intr_list param_cterms
             |> (fn th => th COMP_INCR rule)

structure Val_Counter = Proof_Data (
  type T = int
  val init = K 0
)

fun inc_val_counter ctxt =
  let
    val n = Val_Counter.get ctxt
  in (n, Val_Counter.put (n+1) ctxt)
  end


fun accept_proc (ctxt,sequent) =
  let open PhiSyntax
    val accept_proc_thm = Proof_Context.get_thm ctxt "local.\<phi>accept_proc"
    val rule = (@{print} sequent) RS accept_proc_thm
    val ([(s_name', s_ty), (_, ret_ty)], \<^const>\<open>Pure.imp\<close> $ sequent'_term $ _) =
          NuHelp.strip_binder_raw \<^const_name>\<open>Pure.all\<close> (hd (Thm.prems_of rule))
    val ([s_name,ret_name],ctxt') =
            inc_val_counter ctxt |-> (fn i => Proof_Context.add_fixes
                [(Binding.name s_name', NONE, NoSyn),
                 (Binding.name ("\<v>\<a>\<l>" ^ string_of_int i), SOME ret_ty, NoSyn)])
    val sequent'_cterm =
          Term.subst_bounds ([Free (ret_name, ret_ty), Free (s_name,s_ty)], sequent'_term)
              |> Thm.cterm_of ctxt
    val param_cterms = [Free (s_name,s_ty), Free (ret_name, ret_ty)]
              |> map (Thm.cterm_of ctxt)

    val ([sequent'],ctxt'2) = Assumption.add_assms
          (fn _ => fn [assm] => (export_codeblock ctxt' param_cterms rule assm, I)) [sequent'_cterm] ctxt'
  in
    (ctxt'2, sequent')
  end

(*Param & Label*)
fun param_type sequent =
  NuBasics.param_type sequent
    |> map_atyps (fn ty => case ty of TVar _ => dummyT | _ => ty)
  (* TODO: how to parse (check) the term of a desired type pattern
  * (schematic type variable)? *)



fun set_param' ctxt term sequent =
    (term |> Thm.cterm_of ctxt |> NuBasics.intro_param)
      RS sequent

fun set_param term' (ctxt,sequent) =
  let
    val (\<^const>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>ParamTag\<close>, _) $ X)) = Thm.major_prem_of sequent
    val term = term' |> Type.constraint (param_type sequent) |> Syntax.check_term ctxt
  in
    case X
      of Const(\<^const_name>\<open>ExSet\<close>, _) $ (Abs (_,_,(Const(\<^const_name>\<open>ExSet\<close>, _) $ _)))
            => (ctxt, set_param' ctxt term  sequent)
       | Const(\<^const_name>\<open>ExSet\<close>, _) $ _ =>
            let
              val (N,term') = QuantExpansion.aggregate_variables_quantification term
            in (ctxt, set_param' ctxt term' sequent
                        |> Raw_Simplifier.rewrite_rule ctxt
                              (QuantExpansion.ExNu_expansion N ctxt
                            :: QuantExpansion.forall_expansion N ctxt
                            :: QuantExpansion.pure_All_expansion N ctxt
                            :: QuantExpansion.exists_expansion N ctxt
                            :: QuantExpansion.aux_expansions ctxt))
            end
       | _ => (ctxt, set_param' ctxt term sequent)
  end

fun set_param_cmd term (ctxt,sequent) =
  case try (dest_funT #> apfst PhiSyntax.dest_named) (param_type sequent)
    of SOME (name_and_tys, rng) =>
        let
          val fixes = map (fn (name,ty) =>
                (Binding.name name, (if ty = dummyT then NONE else SOME ty), NoSyn)) name_and_tys
          val (fixed_names, ctxt) = Proof_Context.add_fixes fixes ctxt
          val term = Syntax.parse_term ctxt term
                      |> NuHelp.tuple_abs (map fst name_and_tys ~~ map (rpair dummyT) fixed_names)
                      |> NuHelp.mk_monop @{const_name case_named}
        in
          set_param term (ctxt,sequent)
        end
     | NONE => set_param (Syntax.parse_term ctxt term) (ctxt,sequent)

fun set_label name (ctxt,sequent) = (ctxt, mk_label_thm name RS sequent)





fun synthesis term (ctxt, sequent) =
  let
    val i_s = Thm.maxidx_of sequent + 1
    val i_t = Thm.maxidx_of_cterm term + 1
    val sequent' = @{thm \<phi>synthesis}
          |> Thm.incr_indexes (i_s + i_t)
          |> Drule.infer_instantiate ctxt [(("X",i_s + i_t), Thm.incr_indexes_cterm i_s term),
                                           (("sequent",i_s + i_t), Thm.cprop_of sequent)]
          |> (fn rule => Thm.implies_elim rule sequent)
  in
    case Nu_Reasoner.reason ~1 (ctxt, sequent')
      of SOME ret => ret
       | NONE => error ("fail to synthesis "^Syntax.string_of_term ctxt (Thm.term_of term))
  end


fun setup_proof print_results mode strict_asm kind before_qed after_qed' fixes assumes gl stat =
  let open Proof
    fun after_qed ctxthms stat =
      stat |> end_block 
           |> after_qed' ctxthms
  in
    stat |> begin_block
      |> internal_goal print_results mode strict_asm kind before_qed after_qed fixes assumes
            (map (pair Binding.empty_atts) gl)
      (* |> apsnd (fn stat => using_facts (Named_Theorems.get (context_of stat)
      * "NuSys.useful") stat) *)
  end

fun obligations_of (\<^const>\<open>Pure.imp\<close>
                    $ (\<^const>\<open>Trueprop\<close> $ (\<^term>\<open>Proof_Obligation\<close> $ G))
                    $ P) = G :: obligations_of P
  | obligations_of _ = []

fun obligation_proof print_results mode strict_asm kind before_qed after_qed fixes assumes sequent =
  let
    val oblgs = obligations_of (Thm.prop_of sequent)
    fun after_qed' (ctxt, thmss) stat =
      let
        val ctxt' = Proof.context_of stat
        val thms = Proof_Context.export ctxt ctxt' (flat thmss)
        val sequent' = fold (fn x => fn s => x RS (@{thm Premise_I} RS s)) thms sequent
       in after_qed sequent' stat
      end
  in
    Proof.internal_goal print_results mode strict_asm kind before_qed after_qed' fixes assumes
       (map (fn t=> (Binding.empty_atts,[(HOLogic.mk_Trueprop t,[])])) oblgs)
  end
  

end