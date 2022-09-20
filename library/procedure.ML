signature NU_PROCEDURE = sig
  val procedure_kind : string
  val cast_kind : string
  val app_suffix : string
  val compilation_suffix : string
  val not_define_new_const : bool Config.T

  val define : Attrib.binding -> thm -> local_theory -> thm * local_theory

  type interface = {name: Binding.binding, thm: thm}
  (*interfaces introduced in this given theory, excluding others inherited from father theories*)
  val interfaces_of : theory -> interface Symtab.table
  (*procedures introduced in this given theory, excluding others inherited from father theories*)
  val procedures_of : Context.generic -> string list (*names*)
  val compilation_thm_of : theory -> string (*name*) -> thm
  val add_interface : interface -> theory -> theory
  (* val add_interface_command : (Binding.binding * string) * (string * string)
  * option -> theory -> theory *)
end

structure NuProcedure : NU_PROCEDURE = struct
open NuBasics

val app_suffix = "_\<phi>app"
val compilation_suffix = "_\<phi>compilation"
val procedure_kind = "\<phi>procedure"
val cast_kind = "\<phi>cast"
(* val compilation_thm = gen_get_thm compilation_suffix
fun compilation_thm_of ctx tm = compilation_thm ctx (term_name tm,
  Position.none) *)


type interface = {name: Binding.binding, thm: thm}

(*All interfaces to be exported in *a* theory*)
structure Interfaces = Theory_Data(
  type T = interface Symtab.table Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (K false)
)

(*All interfaces to be exported in *a* theory*)
structure Procedures = Generic_Data(
  type T = string list Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (K false)
)

val thy_name_of_ctxt = Context.theory_long_name o Context.the_theory

fun interfaces_of thy =
  the_default Symtab.empty (Symtab.lookup (Interfaces.get thy) (Context.theory_long_name thy))
fun procedures_of ctxt =
  the_default [] (Symtab.lookup (Procedures.get ctxt) (thy_name_of_ctxt ctxt))
fun compilation_thm_of thy name =
      Global_Theory.get_thm thy (suffix compilation_suffix name)
fun add_interface intrf thy =
  Interfaces.map (Symtab.map_default 
    (Context.theory_long_name thy, Symtab.empty)
    (Symtab.insert (K false) (Binding.name_of (#name intrf), intrf))) thy
fun add_procedure name ctxt =
  Procedures.map (Symtab.map_default (thy_name_of_ctxt ctxt, [])
    (fn l => name :: l)) ctxt

(* fun add_interface_command ((name,const),tys) thy =
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
                $ NuBasics.mk_label (Binding.name_of name)
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

val not_define_new_const = Attrib.setup_config_bool \<^binding>\<open>\<phi>not_define_new_const\<close> (K false);

fun norm_def ctxt (m,n,instance) def = let
  val vars = strip_abs_vars (Logic.dest_equals (Thm.concl_of def) |> #2)
  val ty_vars = take m vars
        |> map (fn (_, ty) => Thm.cterm_of ctxt (Const ("Pure.type", ty)))
  val normal_vars = take n (drop m vars)
        |> map (fn (name,ty) => Thm.var ((name,0), Thm.ctyp_of ctxt ty))
  val insts = ty_vars @ normal_vars @ [Thm.cterm_of ctxt instance]
  in
    fold (fn a => fn b => Thm.combination b a) (map Thm.reflexive insts) def
      |> Raw_Simplifier.rewrite_rule ctxt @{thms \<phi>V_simps[folded atomize_eq]}
  end

fun concl_of (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_,_,x)) = concl_of x
  | concl_of (\<^const>\<open>Pure.imp\<close> $ _ $ x) = concl_of x
  | concl_of x = x


fun closure ctxt f =
  let
    val tvars = Term.add_tvars f []
    val (subst,_) = Term.fold_types Term.declare_typ_names f Name.context
                    |> pair []
                    |> fold_rev (fn ((name,idx),sort) => fn (L,ctxt) =>
                          Name.variant name ctxt
                            |> apfst (fn name' =>
                                  (((name,idx),sort), TFree (name',sort))::L)
                     ) tvars
    val f' = Term_Subst.instantiate (TVars.make subst, Vars.empty) f

    val (instance,f'') = Procedure_Syntax.abstract_return_vals "\<a>\<r>\<g>" false f'
    val vars = fold_aterms (fn Var (name, T) => insert (op =) (name, T)
                             | _ => I) f'' []
    fun abst i (Var v) =
         (case find_index (fn x => x = v) vars
            of ~1 => raise Fail "bug!"
             |  j => Bound (j + i))
      | abst i (A $ B) = abst i A $ abst i B
      | abst i (Abs (name,ty,X)) = Abs (name,ty,abst (i+1) X)
      | abst _ X = X

  in abst 0 f''
      |> fold (fn ((name,_), T) => fn X => Abs (name, T, X)) vars
      |> fold (fn (_,tfree) => fn x => Abs ("_", Type ("itself", [tfree]), x)) subst
      |> pair (length tvars, length vars, instance)
  end

fun gen_define (binding,attrs) sequent lthy =
  let
    val sequent' = sequent
          |> Drule.zero_var_indexes
    val (f,_,_,_) = Thm.concl_of sequent' |> concl_of |> PhiSyntax.dest_procedure 


    (*all variables in the procedure body*)
    (*then f' is the standard form of a definition*)
    val (arity_ins,f') = closure lthy f

    val (def_binding,proc_binding) = if Binding.is_empty binding
                                     then (binding,binding)
                                     else (Binding.suffix_name compilation_suffix binding
                                          ,Binding.suffix_name app_suffix binding)

    (*replace the procedure body in the procedural theorem to the newly defined constant*)
    val rename_proc = Proof_Context.get_thm lthy "local.\<phi>rename_proc"
    val rename_proc' = Proof_Context.get_thm lthy "local.\<phi>rename_proc_with_goal"
    fun rename def proc_th =
          (proc_th RS (def RS rename_proc))
          handle THM _ => (proc_th RS (def RS rename_proc'))

    val (lthy, sequent'') =
      if Binding.is_empty binding orelse Config.get lthy not_define_new_const
      then (lthy, sequent')
      else lthy
            |> Local_Theory.define ((binding, NoSyn), ((def_binding,[]), f'))
            |-> (fn (tm,(_,def)) => fn lthy_x => 
                lthy_x
                  |> Local_Theory.background_theory
                        (Context.theory_map (add_procedure (Binding.name_of binding)))
                  |> rpair (rename (norm_def lthy_x arity_ins def) sequent')
                )

    (*val sequent = sequent
          |> Raw_Simplifier.rewrite_rule lthy @{thms atomize_imp}
          |> Raw_Simplifier.rewrite_rule lthy
              (Proof_Context.get_thms lthy "NuSys.final_proc_rewrite")
          |> Raw_Simplifier.rewrite_rule lthy
              (Proof_Context.get_thms lthy "NuSys.final_proc_rewrite2") *)
  in lthy |> Local_Theory.notes_kind procedure_kind
                [((proc_binding,attrs), [([sequent''],[])])]
          |> apfst (fn [(_,[sequent''''])] => sequent'''')
  end

fun define binding =
  if Binding.is_empty_atts binding then pair else gen_define binding

end
