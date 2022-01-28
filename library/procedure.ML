signature NU_PROCEDURE = sig
  val procedure_kind : string
  val cast_kind : string
  val app_suffix : string
  val compilation_suffix : string
  val define : Attrib.binding -> thm -> local_theory -> thm * local_theory

  type interface = {name: Binding.binding, thm: thm}
  (*interfaces introduced in this given theory, excluding others inherited from father theories*)
  val interfaces_of : theory -> interface Symtab.table
  (*procedures introduced in this given theory, excluding others inherited from father theories*)
  val procedures_of : Context.generic -> string list (*names*)
  val compilation_thm_of : theory -> string (*name*) -> thm
  val add_interface : interface -> theory -> theory
  val add_interface_command : (Binding.binding * string) * (string * string) option -> theory -> theory
end

structure NuProcedure : NU_PROCEDURE = struct
open NuBasics

val app_suffix = "_\<nu>app"
val compilation_suffix = "_\<nu>compilation"
val procedure_kind = "\<nu>procedure"
val cast_kind = "\<nu>cast"
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
    val const = if is_TFree ty orelse is_TVar ty
                then Term.subst_atomic_types [(ty, @{typ void})] const (*set tail to void*)
                else const
    val const = Thm.cterm_of ctxt (Logic.varify_types_global const) |> Drule.mk_term


    fun modify_tail ty =
      let
        val tys = HOLogic.strip_tupleT ty
      in
        if last tys = @{typ void} then ty else HOLogic.mk_tupleT (tys @ [@{typ void}])
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



fun norm_def ctxt (m,n) def = let
  val vars = strip_abs_vars (Logic.dest_equals (concl_of def) |> #2)
  val ty_vars = take m vars
        |> map (fn (_, ty) => cterm_of ctxt (Const ("Pure.type", ty)))
  val normal_vars = take n (drop m vars)
        |> map (fn (name,ty) => Thm.var ((name,0), ctyp_of ctxt ty))
  in
    fold (fn a => fn b => Thm.combination b a)
            (map reflexive (ty_vars @ normal_vars)) def
  end

fun define (binding,attrs) proc_th lthy =
  let
    val proc_th = proc_th
          |> Raw_Simplifier.rewrite_rule lthy
              (Proof_Context.get_thms lthy @{named_theorems final_proc_rewrite})
          |> Drule.zero_var_indexes
    val (f,U,V) = Thm.concl_of proc_th |> dest_procedure 

    (*all variables in the procedure body*)
    val vars = fold_aterms (fn Var v => insert (op =) (Var v)
                             | Free v => insert (op =) (Free v)
                             | _ => I) f []
    fun lambda v body = Abs (term_name v, fastype_of v, abstract_over (v,body))
    (*then f' is the standard form of a definition*)
    val f' = fold lambda vars f |> Logic.unvarify_types_global
    val tvars = add_tfrees f' []
    val f' = fold (fn v => fn x => Abs ("_", Type ("itself", [TFree v]), x)) tvars f'
    val arity = (length tvars, length vars)

    val def_binding = Binding.suffix_name compilation_suffix binding
    val proc_binding = Binding.suffix_name app_suffix binding

    (*replace the procedure body in the procedural theorem to the newly defined constant*)
    fun rename def proc_th = proc_th RS (def RS @{thm rename_proc})

    val (lthy, proc_th) =
      if Binding.is_empty binding then (lthy, proc_th)
      else lthy
            |> Local_Theory.define ((binding, NoSyn), ((def_binding,[]), f'))
            |-> (fn (tm,(_,def)) => 
                  Local_Theory.background_theory (Context.theory_map
                                      (add_procedure (Binding.name_of binding)))
                  #> rpair (rename (norm_def lthy arity def) proc_th))

    val proc_th = proc_th
          |> Raw_Simplifier.rewrite_rule lthy @{thms atomize_imp}
          (* |> Raw_Simplifier.rewrite_rule lthy
              (Proof_Context.get_thms lthy "NuSys.final_proc_rewrite")
          |> Raw_Simplifier.rewrite_rule lthy
              (Proof_Context.get_thms lthy "NuSys.final_proc_rewrite2") *)
  in lthy |> Local_Theory.notes_kind procedure_kind
                [((proc_binding,attrs), [([proc_th],[])])]
          |> apfst (fn [(_,[proc_th])] => proc_th)
  end

end
