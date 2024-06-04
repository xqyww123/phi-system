
structure Phi_Procedure : PHI_PROCEDURE = struct
open Phi_Procedure Phi_Envir





(*
fun add_interface_command ((name,const),tys) thy =
  let
    val ctxt = Proof_Context.init_global thy
          |> Proof_Context.set_mode Proof_Context.mode_schematic

    (*prepare const*)
    fun prep_const const = case fastype_of const of Type ("fun", [T as Type("itself", _ ), _ ]) =>
                                  prep_const (const $ Const("Pure.type", T))
                            | _ => const
    val const = Syntax.read_term_global thy const |> prep_const
    val ty = case fastype_of const
               of Type ("fun", [ty, _ ]) => ty
                | ty => raise TYPE ("bad type: not a procedure", [ty], [const])
    val ty = HOLogic.strip_tupleT ty |> List.last
    (* TODO: FIX ME *)
    (* val const = if is_TFree ty orelse is_TVar ty
                then Term.subst_atomic_types [(ty, typ void)] const (*set tail to void*)
                else const *)
    val const = Thm.cterm_of ctxt (Logic.varify_types_global const) |> Drule.mk_term


    fun modify_tail ty =
      let
        val tys = HOLogic.strip_tupleT ty
      in
        if last tys = typ void then ty else HOLogic.mk_tupleT (tys @ [typ void])
      end
    val (ty_args,ty_rets) =
          the_default (TVar (("'a",0), @{sort lrep}), TVar (("'b",0), @{sort lrep}))
                      (Option.map (apply2 (modify_tail o Syntax.parse_typ ctxt)) tys)
    val goal = mk_Trueprop (Const (@{const_name Prog_Interface}, dummyT)
                $ Phi_Envir.mk_label (Binding.name_of name)
                $ Logic.mk_type ty_args
                $ Logic.mk_type ty_rets
                $ Var(("proc_or_func", 0), dummyT))
          |> Syntax.check_term ctxt


    val thm = (const RS @{thm Prog_Interface_func})
          handle THM _ => const RS @{thm Prog_Interface_proc}
    val thm = thm RS Thm.trivial (Thm.cterm_of ctxt goal)


    val intrf = Thm.prop_of thm
    val _ = if null (Term.add_tfrees intrf []) andalso null (Term.add_tvars intrf []) then ()
            else raise TERM ("free type vars in an interface to be exported", [intrf])
  in
    add_interface {name = name, thm = thm} thy
  end
*)

end