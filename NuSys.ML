(* The Signature *)
signature NU_SYS = sig
  (** Tactics **)
  exception CastFail of cterm * thm
  exception ReasoningFail of thm

  (** Basic Operations **)
  val cast : cterm (*desired nu*) -> context_state (*sequent*) -> context_state

  val accept_proc : context_state -> context_state

  val set_param : term -> context_state -> context_state
  val set_param_cmd : string -> context_state -> context_state
  val set_label : string -> context_state -> context_state

  val start_proc : string (*blk name*) -> cterm -> Proof.context -> context_state

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
exception CastFail of cterm * thm
exception ReasoningFail of thm

(*fun print_dbg' th = Seq.make (fn () => (@{print} th; NONE))
fun print_dbg'' th = Seq.make (fn () => (@{print} th; raise NDBG th))
fun print_dbg th = Seq.make (fn () => (@{print} th; SOME (th, Seq.empty))) *)

(** Basic Operations **)

fun cast desired_nu (ctxt,sequent) =
  let
    val if_current_construction = can (PhiSyntax.dest_CurrentConstruction) (Thm.prop_of sequent)
    val rule =(if if_current_construction
               then Proof_Context.get_thm ctxt "local._\<phi>cast_internal_rule_"
               else Proof_Context.get_thm ctxt "local._\<phi>cast_internal_rule_'")
              |> Drule.infer_instantiate ctxt [(("T'",0),desired_nu)]
    val (ctxt', sequent') =
          case Nu_Reasoner.reason (ctxt, sequent RS rule)
            of SOME ret => ret
             | NONE => raise CastFail (desired_nu, sequent)
    val _ = case Thm.prop_of sequent'
              of (\<^const>\<open>Trueprop\<close> $ _) => ()
               | (\<^const>\<open>Pure.imp\<close>
                    $ (\<^const>\<open>Trueprop\<close> $ (\<^term>\<open>Proof_Obligation\<close> $ _))
                    $ (\<^const>\<open>Trueprop\<close> $ _)) => ()
               | _ => raise CastFail (desired_nu, sequent)
  in (ctxt',sequent') end

fun export_codeblock _ param_cterms rule assm sequent =
     sequent |> Thm.implies_intr assm
             |> Drule.forall_intr_list param_cterms
             |> (fn th => th COMP rule)

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
    val rule = sequent RS accept_proc_thm
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

fun set_param term (ctxt,sequent) =
  (ctxt,
    (term |> Type.constraint (param_type sequent)
          |> Syntax.check_term ctxt |> Thm.cterm_of ctxt |> NuBasics.intro_param)
      RS sequent)

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

fun finish_proc cc (ctxt,sequent) =
  let open PhiSyntax
    val reassemble_proc_final = Proof_Context.get_thm ctxt "local.\<phi>reassemble_proc_final"
    val (_,s',H',_) = dest_CurrentConstruction_c cc
  in
    sequent
      |> Thm.implies_intr cc
      |> Thm.forall_intr H'
      |> Thm.forall_intr s'
      |> (fn th => th COMP reassemble_proc_final)
      |> pair ctxt
  end


fun start_proc blk_name arg_nuTy ctxt =
  let open PhiSyntax
    val ([blk_name, RR],ctxt) = Variable.add_fixes [blk_name, "\<RR>"] ctxt
    val stat_var = Free (blk_name, mk_resourceT ctxt)
    val ctxt = Variable.declare_constraints stat_var ctxt
    val init = Const("local.CurrentConstruction",
                      \<^typ>\<open>mode\<close>
                  --> fastype_of stat_var
                  --> dummyT
                  --> typ_of_cterm arg_nuTy
                  --> \<^typ>\<open>bool\<close>)
               $ \<^const>\<open>programming_mode\<close>
               $ stat_var
               $ Free (RR, dummyT)
    val init = Thm.cterm_of ctxt (Syntax.check_term ctxt init)
    val init = Thm.apply @{cterm Trueprop} (Thm.apply init arg_nuTy)
    val ([init],ctxt) = Assumption.add_assms
          (fn _ => fn [cc] => (snd o finish_proc cc o pair ctxt, I)) [init] ctxt
  in
    (ctxt,init)
  end


fun synthesis term (ctxt, sequent) =
  let
    val rule = @{thm \<phi>synthesis}
          |> Drule.infer_instantiate ctxt [(("X",0),term), (("sequent",0), Thm.cprop_of sequent)]
    val sequent' = Thm.implies_elim rule sequent
  in
    case Nu_Reasoner.reason (ctxt, sequent')
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